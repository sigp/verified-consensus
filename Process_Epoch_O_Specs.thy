theory Process_Epoch_O_Specs
imports ProcessEpoch_O sqrt_proof
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
  by (simp add: word_sub_le_iff)
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
  apply (clarsimp)
  apply (rule hoare_weaken_pre, assumption)
  apply (clarsimp)
  done




definition "lists_of S \<equiv> {xs. distinct xs \<and> list.set xs = S}"

lemma maps_to_is_valid:"(maps_to l v \<and>* R) s \<Longrightarrow> valid (l) (Some v)"
  apply (clarsimp simp: sep_conj_def maps_to_def )
  sorry

lemma valid_validator_some_simp[simp]: 
"valid validators (Some xs) = (let ys = Invariants.var_list_inner xs in sum_list (map (unat o Validator.effective_balance_f) ys) < 2^(64) \<and> distinct ys \<and> length ys < 2^64 )"
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

find_theorems select


lemma select_wp_lift[wp]: "(\<And>x. x \<in> P \<Longrightarrow> hoare_triple (lift (pre x)) (f x) Q) \<Longrightarrow> hoare_triple (lift (\<lambda>s. \<forall>x\<in>P. pre x s)) (do {x <- select P; f x}) Q"
  apply (clarsimp simp: select_def bindCont_def hoare_triple_def run_def)
  apply (subst Sup_le_iff)
  apply (clarsimp)
  apply (atomize, erule allE, drule mp, assumption)
  apply (erule order_trans)
  apply (rule seq_mono_left)
  by (subst assert_iso[symmetric], clarsimp)


lemma get_total_balance_wp[wp]:"(\<And>x xs (v :: Validator VariableList). distinct xs \<Longrightarrow> list.set xs = S \<Longrightarrow> x = max (EFFECTIVE_BALANCE_INCREMENT config) (sum_list (map (Validator.effective_balance_f \<circ> unsafe_var_list_index v) xs)) \<Longrightarrow>
    hoare_triple (lift (P x)) (f x) Q) 
  \<Longrightarrow> hoare_triple (lift ((maps_to validators v \<and>* (maps_to validators v \<longrightarrow>* (\<lambda>s. (\<forall>x\<in>S. x < var_list_len v) \<and>  ((\<forall>x\<in>S. x < var_list_len v) \<longrightarrow> (\<forall>xs\<in>lists_of S. P (max (EFFECTIVE_BALANCE_INCREMENT config) (sum_list (map (Validator.effective_balance_f \<circ> unsafe_var_list_index v) xs))) s)  )))) ))
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

lemma div_wp_lift: "hoare_triple (lift (P (n div m))) (c (n div m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. m \<noteq> 0 \<and> (m \<noteq> 0 \<longrightarrow>  (P ( n div m)) s))) 
(do {x <- (word_unsigned_div n m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold word_unsigned_div_def, wp)
  apply (clarsimp simp: bindCont_return')
  apply (clarsimp simp: lift_def)
  done

find_theorems name:div_wp

lemma [simp]: "CHURN_LIMIT_QUOTIENT config \<noteq> 0" sorry

lemma get_validator_churn_limit_fast_spec: "hoare_triple (\<lless>num_active_validators \<mapsto>\<^sub>l n \<and>* R\<then>) get_validator_churn_limit_fast (lift (num_active_validators \<mapsto>\<^sub>l n \<and>* R))"
  apply (clarsimp simp: get_validator_churn_limit_fast_def, rule hoare_weaken_pre)
   apply (wp)
   apply (rule div_wp_lift)
   apply (rule return_wp)
  apply (clarsimp)
  apply (sep_solve)
  done

lemma get_validator_churn_limit_fast_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow> 
     hoare_triple (\<lless>num_active_validators \<mapsto>\<^sub>l n \<and>* (num_active_validators \<mapsto>\<^sub>l n \<longrightarrow>* P (max (MIN_PER_EPOCH_CHURN_LIMIT config) (n div CHURN_LIMIT_QUOTIENT config)))\<then>) 
      (bindCont get_validator_churn_limit_fast c) (Q)"
  apply (clarsimp simp: get_validator_churn_limit_fast_def, rule hoare_weaken_pre)
   apply (wp)
   apply (rule div_wp_lift)
  apply (fastforce)
  apply (clarsimp)
  apply (sep_cancel)+
  done

lemma get_validator_churn_limit_spec: "hoare_triple (\<lless>beacon_slots \<mapsto>\<^sub>l v \<and>* validators \<mapsto>\<^sub>l vs \<and>*  R\<then>) get_validator_churn_limit (lift (beacon_slots \<mapsto>\<^sub>l v \<and>* validators \<mapsto>\<^sub>l vs \<and>* R))"
  apply (clarsimp simp: get_validator_churn_limit_def, rule hoare_weaken_pre)
   apply (wp)
   apply (rule div_wp_lift)
   apply (rule return_wp)
  apply (clarsimp)
  apply (sep_cancel)+
  done

lemma get_validator_churn_limit_spec': "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (\<lless>beacon_slots \<mapsto>\<^sub>l v \<and>* validators \<mapsto>\<^sub>l vs \<and>* (beacon_slots \<mapsto>\<^sub>l v \<and>* validators \<mapsto>\<^sub>l vs \<longrightarrow>* P (max (MIN_PER_EPOCH_CHURN_LIMIT config) (word_of_nat (length (active_validator_indices (slot_to_epoch config v) vs)) div CHURN_LIMIT_QUOTIENT config))) \<then>) (bindCont get_validator_churn_limit c) (Q)"
  apply (clarsimp simp: get_validator_churn_limit_def, rule hoare_weaken_pre)
   apply (wp)
   apply (rule div_wp_lift)
  apply (assumption)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (sep_cancel)+
  done

lemma [simp]: "\<lless>\<lambda>s. P\<then> = (\<lambda>s. P)" 
  apply (intro ext, clarsimp simp: lift_def)  
  apply (safe)
  apply (rule_tac x="id_p" in exI)
  by simp

lemma add_wp[wp]: "hoare_triple (lift (P (n + m))) (c (n + m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. n \<le> n + m \<and> (n \<le> n + m \<longrightarrow> P (n + m) s))) 
(do {x <- (word_unsigned_add n  m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp:  word_unsigned_add_def )
   apply (simp only: Let_unfold)
   apply (wp, clarsimp simp: bindCont_return')
  done

lemma mod_wp[wp]: "hoare_triple (lift (P (n mod m))) (c (n mod m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. m \<noteq> 0 \<and> (m \<noteq> 0 \<longrightarrow> P (n mod m) s)))
(do {x <- (n .% m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold word_unsigned_mod_def)
   apply wp
  apply fastforce
  done

find_theorems name:if_wp

thm wp

lemma when_wp[wp]: 
  "(B \<Longrightarrow> hoare_triple  ( lift S) ( bindCont P c) R) \<Longrightarrow> (\<not>B \<Longrightarrow> hoare_triple ( lift S') (c ()) R) \<Longrightarrow>
   hoare_triple ( lift (if B then S else S'))  (do {x <- (when B P); c x}) R"
  apply (clarsimp split: if_splits)
  done

definition "next_epoch b_slots \<equiv> epoch_to_u64 (slot_to_epoch config b_slots) + 1"

lemma SLOTS_PER_EPOCH_ATLEAST[simp]: "1 < SLOTS_PER_EPOCH config" sorry
lemma EPOCHS_PER_ETH1_VOTING_PERIOD_ATLEAST[simp]: "EPOCHS_PER_ETH1_VOTING_PERIOD config \<noteq> 0" sorry

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
     apply (metis bits_div_0 div_less_dividend_word less_is_non_zero_p1 lt1_neq0 olen_add_eqv word_less_1 zero_neq_one)
    apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp simp: next_epoch_def)
  by (sep_cancel)+

thm get_previous_epoch_wp

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
  apply (intro conjI impI)
  apply (clarsimp)
   apply (clarsimp simp: previous_epochs_def)
  using less_eq_Epoch_def apply blast
   apply (clarsimp)
   apply (sep_mp)
   apply (clarsimp simp: raw_epoch_simp)
   apply (clarsimp simp: raw_epoch_simp)
  done


abbreviation (input) "sep_wp pre post P \<equiv> (lift (pre \<and>* (post \<longrightarrow>* P)))"

lemma lift_pure_conj[simp]: "lift (\<lambda>s. P \<and> Q s) s = (P \<and> lift Q s)"
  by (clarsimp simp: lift_def)

lemma lift_pure_imp[simp]: "lift (\<lambda>s. P \<longrightarrow> Q s) s = (P \<longrightarrow> lift Q s)"
  apply (clarsimp simp: lift_def)
  apply (safe, blast)
  apply (rule_tac x=id_p in exI)
   apply (clarsimp)
  apply (blast)
  done


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
  by (metis (no_types, opaque_lifting) SLOTS_PER_EPOCH_ATLEAST add.commute
             bits_div_0 div_less_dividend_word inc_i le_no_overflow lt1_neq0
                                    verit_comp_simplify1(2) word_le_not_less)


lemma subst_in_impl: "(x = y \<longrightarrow> f y) = (x = y \<longrightarrow> f x)"
  by (safe)

lemma hoare_eqI': "hoare_triple (lift (P x)) (f x) Q \<Longrightarrow> hoare_triple (lift (\<lambda>s. v = x \<and> (v = x \<longrightarrow> P v s))) (f v) Q"
  apply (rule hoare_assert_stateI)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (erule hoare_weaken_pre)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

lemma hoare_eqI'': "hoare_triple (lift (P x v)) (f x) Q \<Longrightarrow> hoare_triple (lift (\<lambda>s. v = x \<and> (v = x \<longrightarrow> P x v s))) (f v) Q"
  apply (rule hoare_assert_stateI)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (erule hoare_weaken_pre)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

schematic_goal new_state_context_wp[simplified subst_in_impl, wp]: 
 "hoare_triple (lift (pre ?x)) (c ?x) post \<Longrightarrow> hoare_triple (lift ?P) (bindCont new_state_context c) (post)"
  apply (unfold new_state_context_def epoch_unsigned_add_def, rule hoare_weaken_pre)
   apply (wp)
  apply (erule hoare_eqI')
  apply (clarsimp simp: subst_in_impl)
  apply (sep_cancel)+
  done

definition "safe_mul m n \<equiv> if (m = 0 \<or> n = 0) then True else (m * n div n = m)"

lemma fail_wp[wp]: "\<lblot>lift \<bottom>\<rblot> bindCont fail c \<lblot>Q\<rblot>"
  apply (rule hoare_weaken_pre, wp)
  apply (clarsimp simp: lift_def)
  done

thm mul_wp

lemma mul_wp[wp]: "hoare_triple (lift (P (n * m))) (c (n * m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. safe_mul m n  \<and> (safe_mul m n  \<longrightarrow> P (n * m) s))) 
(do {x <- (word_unsigned_mul n m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold  word_unsigned_mul_def )
   apply (simp only: Let_unfold)
   apply (rule if_wp, simp)
    apply (fastforce)
   apply (rule if_wp, simp)
   apply (wp)
  apply (clarsimp simp: safe_mul_def)
  apply (intro conjI impI; clarsimp?)
  by (simp add: mult.commute)

lemma div_wp[wp]: "hoare_triple (lift (P (n div m))) (c (n div m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. m \<noteq> 0 \<and> (m \<noteq> 0 \<longrightarrow> P ( n div m) s))) 
(do {x <- (word_unsigned_div n m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold word_unsigned_div_def, wp)
   apply (clarsimp simp: bindCont_return')
  done

lemma slashings_wf: "(slashings \<mapsto>\<^sub>l ss \<and>* R) s \<Longrightarrow> 
sum_list (map unat (local.vector_inner ss)) \<le> 2 ^ 64 - 1 \<and> 
PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX = sum_list (local.vector_inner ss) *
PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX div sum_list (local.vector_inner ss)"
  sorry

schematic_goal new_slashings_context_wp[wp]: 
  "hoare_triple (lift (P x)) (c x) Q \<Longrightarrow> hoare_triple (lift (slashings \<mapsto>\<^sub>l ss \<and>* ?R)) (bindCont (new_slashings_context st_ctxt pbc) c) ( Q)"
  apply (clarsimp simp: new_slashings_context_def, rule hoare_weaken_pre , wp)
   apply (erule hoare_eqI')
  apply (clarsimp)
  apply (frule slashings_wf)
  apply (erule sep_conj_impl, assumption)
  apply (clarsimp)
  apply (assumption)
  done


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
  apply (sep_mp, clarsimp)
  done

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
  apply (sep_cancel)+
  apply (intro conjI impI)
  apply (sep_mp)
  apply (clarsimp)
   apply (clarsimp simp: frequency_map_def exit_cache_eq_iff ExitCache.defs)
   apply (intro ext, clarsimp)
  apply (sep_mp, clarsimp)
  done


lemma mapM_wp'':
  assumes c_wp: "\<And>(f :: 'e \<Rightarrow> ('f, 'a) cont) x P Q.  (\<And>xs. hoare_triple (lift (P (g x))) (f (g x)) ( Q)) \<Longrightarrow> hoare_triple (lift (pre x)) (do { b <- c x; f b}) Q"  
shows "  (\<And>x y. hoare_triple (lift (P x)) (f y) Q) \<Longrightarrow>   hoare_triple (lift (\<lambda>s. (\<forall>x\<in>list.set xs. pre x s) \<and> ((\<forall>x\<in>list.set xs. pre x s) \<longrightarrow> P (map g xs) s))) (do {vs <- mapM c (xs :: 'd list) ; (f :: 'e list \<Rightarrow> ('f, 'a) cont) (vs )}) Q"
  apply (induct xs arbitrary: f)
   apply (simp)
  apply (clarsimp)
  apply (rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric])
   apply (rule c_wp)
  defer
    apply (clarsimp)
  defer
  apply (atomize)
  apply (erule_tac x="(\<lambda>aa. f (g a # aa))" in allE)
  apply (drule mp)
   apply (clarsimp)
  apply (fastforce)
  done

thm mapM_wp

term "foldr (\<lambda>x R. pre' R x) xs"

lemma mapM_wp_foldr:
  assumes c_wp: "\<And>(f :: 'e \<Rightarrow> ('f, 'a) cont) x P Q. (\<And>x. hoare_triple (lift (P)) (f x) (Q)) \<Longrightarrow> hoare_triple (lift (pre P x)) (do { b <- c x; f b}) Q"  
shows " (\<And>x. hoare_triple (lift (P)) (f x) Q) \<Longrightarrow>   hoare_triple (lift (foldr (\<lambda>x R. pre R x) xs P )) (do {vs <- mapM c (xs :: 'd list) ; (f :: 'e list \<Rightarrow> ('f, 'a) cont) (vs )}) Q"
  apply (induct xs arbitrary: f; clarsimp)
  by (metis (no_types, lifting) bindCont_assoc c_wp return_triple')

lemma mapM_wp':
  assumes c_wp: "\<And>(f :: 'e \<Rightarrow> ('f, 'a) cont) x P Q. hoare_triple (lift P) (f (g x)) ( Q) \<Longrightarrow> hoare_triple (lift (pre P x)) (do { b <- c x; f b}) Q"  
  assumes pre_mono: "(\<And>x P Q s . (P s  \<Longrightarrow> Q s) \<Longrightarrow>  (pre P x) s \<Longrightarrow>  (pre Q x) s  )"
shows " hoare_triple (lift P) (f (map g xs)) Q \<Longrightarrow>   hoare_triple (lift (\<lambda>s. (\<Sqinter>x\<in>(list.set xs). pre P x) s \<and> ((\<Sqinter>x\<in>(list.set xs). pre P x) s \<longrightarrow> P s))) (do {vs <- mapM c (xs :: 'd list) ; (f :: 'e list \<Rightarrow> ('f, 'a) cont) (vs )}) Q"
  apply (induct xs arbitrary: f; clarsimp)
  apply (atomize)
  apply (clarsimp simp: bindCont_assoc[symmetric])
  apply (rule hoare_weaken_pre)
  apply (rule c_wp)
  apply (erule allE)
  apply (erule impE)
   defer
    apply (assumption)
   apply (clarsimp)
   apply (rule pre_mono[rotated], assumption)
   apply (clarsimp)
  
  apply (clarsimp)
  done

lemma ebi_not_zero[intro]: "EFFECTIVE_BALANCE_INCREMENT config \<noteq> 0" sorry

lemma brf_ebi_times_bounded[simp]: 
      "EFFECTIVE_BALANCE_INCREMENT config * 
       BASE_REWARD_FACTOR config div EFFECTIVE_BALANCE_INCREMENT config = 
       BASE_REWARD_FACTOR config" sorry

lemma sqrt_eq_zero_iff[simp]: "sqrt' x = 0 \<longleftrightarrow> x = 0"
  by (metis (no_types, opaque_lifting) add_0 bits_div_by_1
   comm_monoid_mult_class.mult_1 linorder_not_le lt1_neq0 
       sqrt_induct sqrt_le sub_wrap word_not_simps(1))

definition "mul_bound x y \<equiv> y = x * y div x"

lemma safe_mul_commute: "safe_mul (x :: u64) y = safe_mul y x"
  apply (clarsimp simp: safe_mul_def)
  apply (safe)
   apply (unat_arith, simp)
   apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum div_mult_le mult.commute
        nonzero_mult_div_cancel_left order_le_less_trans unat_mult_lem unsigned_less)
 apply (unat_arith, simp)
   apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum div_mult_le mult.commute
        nonzero_mult_div_cancel_left order_le_less_trans unat_mult_lem unsigned_less)
  done

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
  using ebi_not_zero apply force
   apply (metis brf_ebi_times_bounded mult.commute safe_mul_def)
  using safe_mul_commute by blast

lemma nonempty_ball_conj_lift: "S \<noteq> {} \<Longrightarrow> (\<forall>x\<in>S. P \<and> Q x) = (P \<and> (\<forall>x\<in>S. Q x))"
  by (safe; clarsimp?)


lemma nonempty_ball_imp_lift: "S \<noteq> {} \<Longrightarrow> (\<forall>x\<in>S. P \<longrightarrow> Q x) = (P \<longrightarrow> (\<forall>x\<in>S. Q x))"
  by (safe; clarsimp?)

lemma effective_balance_safe[simp]:
 "MAX_EFFECTIVE_BALANCE \<le> MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config" sorry 

lemma range_empty_iff: " (range x y z) = [] \<longleftrightarrow> (x \<ge> y) \<or> z = 0"
  apply (case_tac z; clarsimp)
  done 

lemma start_in_valid_range[simp]: "range x y z \<noteq> [] \<Longrightarrow> x \<in> list.set (range x y z)"
  apply (clarsimp simp: range_empty_iff)
  by (case_tac z; clarsimp?)

lemma EBI_ge_zero[intro]: "EFFECTIVE_BALANCE_INCREMENT config > 0" sorry

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
  apply (clarsimp simp: compute_base_rewards_def, rule hoare_weaken_pre, wp)
  apply (rule mapM_wp'[where g="(\<lambda>effective_balance. of_nat effective_balance div EFFECTIVE_BALANCE_INCREMENT config * (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)))" for f])
    apply (erule get_base_reward_fast_wp)
    apply (intro conjI impI; clarsimp?)
  apply (fastforce)
   apply (erule hoare_eqI')
  apply (clarsimp)
  apply (erule sep_conj_impl, assumption)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (subgoal_tac "list.set (local.range 0 (unat (MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config)) (unat (EFFECTIVE_BALANCE_INCREMENT config))) \<noteq> {}")
   apply (clarsimp simp: nonempty_ball_conj_lift nonempty_ball_imp_lift)
   apply (erule_tac x=0 in ballE; clarsimp?)
  apply (clarsimp simp: range_empty_iff)
  by (metis (mono_tags, opaque_lifting) add_0
           ebi_not_zero effective_balance_safe gr0I unat_eq_zero word_coorder.extremum_uniqueI)
  

lemma read_beacon_wp_alt[wp]: "(\<And>x. hoare_triple ( lift (P x)) (c x) (Q )) \<Longrightarrow>
   hoare_triple (lift (maps_to l v \<and>* (maps_to l v \<longrightarrow>* (\<lambda>s. x = v \<and> (x = v \<longrightarrow> (P v s)))))) 
  (do {v <- read_beacon l ; c v}) (Q  )"
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
  apply (sep_select_asm 2)
     apply (frule sep_mp)
  apply (clarsimp)
  apply (sep_mp, clarsimp)
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
  sorry
   apply (drule maps_to_get_wf, clarsimp)
  apply (drule maps_to_get_wf, clarsimp)
  done

abbreviation "map_var f vs \<equiv> map f (var_list_inner vs)"

text \<open>[where x=x and v="\<lparr> effective_balances_f = (map_var Validator.effective_balance_f vs), 
      base_rewards_f = (map (\<lambda>effective_balance.
                             word_of_nat effective_balance div EFFECTIVE_BALANCE_INCREMENT config * (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)))
                      (local.range 0 (unat (MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config)) (unat (EFFECTIVE_BALANCE_INCREMENT config)))) \<rparr>"\<close>


thm hoare_assert_stateI

lemma hoare_eqI''': "hoare_triple (lift (P x)) (f x) Q \<Longrightarrow> v = x \<Longrightarrow>  hoare_triple (lift (P v)) (f v) Q"
  apply (rule hoare_assert_stateI)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (erule hoare_weaken_pre)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

lemma hoare_eqI_weaken: "hoare_triple (lift (P x)) (f x) Q \<Longrightarrow> (\<And>s. P' v s \<Longrightarrow> P x s) \<Longrightarrow> hoare_triple (lift (\<lambda>s. x = v \<and> (x = v \<longrightarrow> P' v s))) (f v) Q"
  apply (rule hoare_assert_stateI)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (erule hoare_weaken_pre)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

lemma read_beacon_wp'[wp]: "(\<And>x. hoare_triple ( lift (P x)) (c x) (Q )) \<Longrightarrow> 
hoare_triple (lift (maps_to l v \<and>* (maps_to l v \<longrightarrow>*  (P v )))) (do {v <- read_beacon l ; c v}) (Q  )"
  apply (wp)
  done

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

find_theorems get_unslashed_participating_indices

thm get_current_unslashed_participating_indices_wp


abbreviation "current_epoch bs \<equiv> slot_to_epoch config bs"

definition "unslashed_participating_indices flag_index epoch epoch_participation vs  \<equiv>
            {x \<in> list.set (active_validator_indices epoch vs). 
             has_flag (unsafe_var_list_index epoch_participation x) flag_index \<and> 
             \<not> slashed_f (unsafe_var_list_index vs x)} 
            "

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


lemma val_length_wf:  "(validators \<mapsto>\<^sub>l vs \<and>* R) s \<Longrightarrow> length (local.var_list_inner vs) \<le> 2 ^ 64 - 1"
  sorry

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

lemma mapM_wp_foldr':
  assumes c_wp: "\<And>(f :: 'e \<Rightarrow> ('f, 'a) cont) x P Q. (\<And>x. hoare_triple (lift (P x)) (f x) (Q)) \<Longrightarrow> 
                                                    hoare_triple (lift (pre (P (g x)) x)) (do { b <- c x; f b}) Q"  
  shows " (\<And>x. hoare_triple (lift (P x)) (f x) Q) 
          \<Longrightarrow>   hoare_triple (lift (foldr (\<lambda>x R. pre R x) xs (P (map g xs)) ))
                (do {vs <- mapM c (xs :: 'd list) ; (f :: 'e list \<Rightarrow> ('f, 'a) cont) (vs )}) Q"
  apply (induct xs arbitrary: P f; clarsimp)
  apply (rule hoare_weaken_pre, subst bindCont_assoc[symmetric])
   apply (rule c_wp)
   apply (atomize, erule allE)
  apply (erule allE) back
  apply (subst bindCont_assoc[symmetric])
   apply (erule mp)
   apply (clarsimp)
   apply (fastforce)
  apply (fastforce)
  done

lemma sep_factor_foldI':
  "(I \<and>* (foldr (\<lambda>x R. (P x \<and>* (Q x \<longrightarrow>* R))) xs (I \<longrightarrow>* R))) s \<Longrightarrow> (foldr (\<lambda>x R. (I \<and>* P x \<and>* (I \<and>* Q x \<longrightarrow>* R))) xs R) s"
  apply (induct xs arbitrary:s; clarsimp simp:)
   apply (sep_solve)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp simp: sep_conj_ac)
  done

lemma factor_foldr_conj: "(\<forall>x\<in>(list.set xs). P x) \<and> (foldr f xs R) s \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow>  
  (foldr (\<lambda>x R s. P x \<and> f x R s) xs R) s"
  apply (induct xs  arbitrary: s; clarsimp)
  by (metis (mono_tags, lifting) monoD predicate1D predicate1I)


lemma factor_foldr_pure: "(\<forall>x\<in>(list.set xs). P x) \<and> ((\<forall>x\<in>(list.set xs). P x) \<longrightarrow> (foldr f xs R) s) \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow>  
  (foldr (\<lambda>x R s. (P x \<longrightarrow> f x R s) \<and> P x) xs R) s"
  apply (induct xs  arbitrary: s; clarsimp)
  apply (atomize)
  by (metis (mono_tags, lifting) le_boolD le_funE monoD predicate1I)

lemma factor_foldr_conj': "(\<forall>x\<in>(list.set xs). P x) \<and> (foldr f xs R) s \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow>  
  (foldr (\<lambda>x R s. f x R s \<and> P x) xs R) s"
  apply (induct xs  arbitrary: s; clarsimp)
  by (metis (mono_tags, lifting) monoD predicate1D predicate1I)


lemma factor_foldr_sep: "(P \<and>* (foldr f xs (P \<longrightarrow>* R))) s \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow>  (\<And>R a. f a (P \<and>* R) = (P \<and>* f a R)) \<Longrightarrow>   (foldr (\<lambda>x R. P \<and>* (P \<longrightarrow>* f x R)) xs  R) s"
  apply (induct xs  arbitrary: s; clarsimp)
   apply (sep_mp, clarsimp)
  apply (sep_cancel)+
  apply (erule sep_curry[rotated])
  apply (clarsimp simp: sep_conj_ac)
  by (smt (verit, ccfv_threshold) monoE predicate1D predicate1I sep_conj_commute)
  apply (erule_tac x=h in allE)
  apply (drule mp)
   apply (sep_cancel)
  oops

lemma in_set_pure_simp[simp]:"in_set (\<lambda>_. P) s = P"
  by (clarsimp simp: in_set_def)

declare range.simps[simp del ]

lemma foldr_const[simp]: "foldr (\<lambda>_ R. R) xs R = R"
  by (induct xs; clarsimp)


lemma mono_id[simp]: "mono (\<lambda>R. R)" 
   by (rule monoI; clarsimp)


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
   apply (wp)
  apply (rule lift_mono')
  apply (safe)
  apply (simp only: in_set_pure_simp[simp] ebi_not_zero)
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

find_theorems new_effective_balances_ctxt

lemma EBI_multiple_of_HYSTERESIS_QUOTIENT: 
  "\<exists>n. HYSTERESIS_QUOTIENT * n div n = HYSTERESIS_QUOTIENT \<and> EFFECTIVE_BALANCE_INCREMENT config = HYSTERESIS_QUOTIENT * n" sorry

lemma upward_threshold_safe: "((EFFECTIVE_BALANCE_INCREMENT config div HYSTERESIS_QUOTIENT) * HYSTERESIS_UPWARD_MULTIPLIER)
         div (EFFECTIVE_BALANCE_INCREMENT config div HYSTERESIS_QUOTIENT) = HYSTERESIS_UPWARD_MULTIPLIER"
  sorry

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
  apply (clarsimp)
  by (simp add: ebi_not_zero)


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


lemma hoare_let[intro, wp]: "hoare_triple P (bindCont (b a) c) Q \<Longrightarrow> hoare_triple P (bindCont (Let a b) c) Q"
  by (clarsimp simp: Let_unfold)


definition "rewardable (v_info :: ValidatorInfo) flag_index state_ctxt \<equiv> 
              (is_unslashed_participating_index v_info flag_index) \<and>
              \<not>(is_in_inactivity_leak_f state_ctxt)"




lemma if_lift: "(if B then lift P else lift Q) = lift (if B then P else Q)"
  by (intro ext; clarsimp simp: lift_def)

thm mul_wp

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

term case_prod

lemma hoare_case_prod[intro, wp]: "hoare_triple P (bindCont (f (fst x) (snd x)) c) Q \<Longrightarrow> 
  hoare_triple P (bindCont (case_prod f x) c) Q"
  by (clarsimp split: prod.splits)


lemma add_wp'[wp]: "(\<And>x. hoare_triple (lift (P x )) (c x) Q) \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. n \<le> n + m \<and> (n \<le> n + m \<longrightarrow> P (n + m) s))) 
(do {x <- (word_unsigned_add n  m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp:  word_unsigned_add_def )
   apply (simp only: Let_unfold)
   apply (wp, clarsimp simp: bindCont_return')
    apply (fastforce)
   apply (wp)
  by (clarsimp)

lemma ISB_not_zero[simp]:  "INACTIVITY_SCORE_BIAS config \<noteq> 0" sorry

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


lemma read_beacon_wp_ex[wp]: "(\<And>x. hoare_triple ( lift (P x)) (c x) (Q )) \<Longrightarrow> 
hoare_triple (lift ((EXS v. maps_to l v \<and>* (maps_to l v \<longrightarrow>*  (P v ))))) (do {v <- read_beacon l ; c v}) (Q  )"
  sorry  apply (wp)
  done

lemma drop_maps_to_lift: "lift (maps_to l v \<and>* R) s \<Longrightarrow> lift R s"
  apply (clarsimp simp: lift_def)
  apply (clarsimp simp: sep_conj_def maps_to_def)
  apply (rule_tac x=y in exI)
  apply (clarsimp)
  apply (clarsimp simp: point_of_plus_domain_iff)
  by (metis comp_apply point_of_plus_domain_iff sep_add_commute valid_write_write)

find_theorems alloc

lemma "\<lless>\<lambda>s. \<forall>x. P x s\<then> \<ge> (ALLS x. lift (P x))" 
  apply (clarsimp)


  find_theorems lift "\<forall>x. ?P x"

lemma "(\<And>s. lift P s \<Longrightarrow> lift Q s) \<Longrightarrow> lift P \<le> lift Q"
  sledgehammer
  by (simp add: le_funI)
  by blast
  apply (clarsimp)

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


lemma write_beacon_wp': "\<lblot>\<lless>P\<then>\<rblot> c () \<lblot>Q\<rblot> \<Longrightarrow> \<lblot>\<lless>(EXS v. l \<mapsto>\<^sub>l v) \<and>* (l \<mapsto>\<^sub>l v' \<longrightarrow>* P)\<then>\<rblot> bindCont (write_to l v') c \<lblot>Q\<rblot>"
  sorry

lemma maps_exI[sep_cancel]: "(maps_to l v) s \<Longrightarrow> (EXS v. maps_to l v) s"
  by (blast)

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
  apply (unat_arith, simp)
  done

lemmas sum_bounded = sum_bounded_l sum_bounded_r

lemma chain_safe: "x \<le> x + z \<Longrightarrow> z \<ge> y \<Longrightarrow> x \<le> x + (y :: u64)"
  by (unat_arith)

lemmas safe_sum_iff = unat_plus_distrib_bounded[THEN iffD2]


lemma free_wp[wp]:" \<lblot>\<lless>P ()\<then>\<rblot> c () \<lblot>Q\<rblot> \<Longrightarrow> \<lblot>\<lless>\<lambda>s.  ((EXS v. l \<mapsto>\<^sub>l v) \<and>* P ()) s\<then>\<rblot> (bindCont (free l) c) \<lblot>Q\<rblot>" sorry


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
  apply (unfold process_single_reward_and_penalty_def, rule hoare_weaken_pre, wp)
    apply (simp only: Let_unfold)
    apply (clarsimp simp: bindCont_return)
    apply (simp only: bindCont_assoc[symmetric])
    apply (rule mapM_wp_foldr'[where g="\<lambda>_. ()"])
     apply (simp only: bindCont_assoc[symmetric])
     apply (rule get_flag_index_delta_wp_gen)
     apply (simp only: bindCont_assoc[symmetric] | rule read_beacon_wp_ex add_wp' write_beacon_wp' wp | fastforce)+
  apply (simp only: if_lift TIMELY_TARGET_FLAG_INDEX_def TIMELY_HEAD_FLAG_INDEX_def TIMELY_SOURCE_FLAG_INDEX_def)
  apply (clarsimp)
   apply (unfold range_participation_flag_weights_simp[simplified])
   apply (simp only: foldr.simps case_flag_simplifiers)
  apply (intro conjI impI; clarsimp simp: Let_unfold)
  apply ( (sep_cancel | intro conjI impI allI | clarsimp simp:  | (rule exI, sep_cancel+) | (erule sep_curry[rotated, where P="P result" for result]))+,
       (fastforce simp: sum_bounded safe_sum_iff add.assoc | fastforce simp: sum_bounded safe_sum_iff | (rule exI, intro conjI impI) | clarsimp simp: unrewardable_simps )?)+
  apply (clarsimp simp: unrewardable_simps  )
  apply ( (sep_cancel | intro conjI impI allI | clarsimp simp:  | (rule exI, sep_cancel+) | (erule sep_curry[rotated, where P="P result" for result]))+,
       (fastforce simp: sum_bounded safe_sum_iff add.assoc | fastforce simp: sum_bounded safe_sum_iff | (rule exI, intro conjI impI))?)+  
       apply (clarsimp simp: unrewardable_simps  )
  apply ( (sep_cancel | intro conjI impI allI | clarsimp simp:  | (rule exI, sep_cancel+) | (erule sep_curry[rotated, where P="P result" for result]))+,
       (fastforce simp: sum_bounded safe_sum_iff add.assoc | fastforce simp: sum_bounded safe_sum_iff | (rule exI, intro conjI impI))?)+ 
  apply (case_tac "is_unslashed_participating_index validator_info (Suc 0)"; clarsimp?)
  by ( (sep_cancel | intro conjI impI allI | clarsimp simp:  | (rule exI, sep_cancel+) | (erule sep_curry[rotated, where P="P result" for result]))+,
       (fastforce simp: sum_bounded safe_sum_iff add.assoc | fastforce simp: sum_bounded safe_sum_iff | (rule exI, intro conjI impI))?)+ 


find_theorems process_single_inactivity_update
find_theorems process_single_slashing

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
  apply (clarsimp simp: ebi_not_zero Let_unfold)
  apply (intro conjI impI allI; clarsimp simp: saturating_sub_def)
    apply (intro conjI impI allI; clarsimp simp: saturating_sub_def)
  done


lemma "(P -* P \<and>* R) s \<Longrightarrow> (P -* (P \<and>* (P \<longrightarrow>* (P \<and>* R)))) s"
  apply (rule septract_cancel[rotated], assumption)
   apply (rule sep_conj_impl[rotated], assumption)
    apply (erule sep_curry', assumption, assumption)
  done

lemma "(P -* P \<and>* R) s \<Longrightarrow> (P -* (P \<and>* (P \<longrightarrow>* R))) s"
  apply (rule septract_cancel, assumption, assumption)
  apply (sep_cancel)
  apply (clarsimp simp: sep_conj_def sep_impl_def)
  oops

lemma "(P \<and>* R) s \<Longrightarrow> (P \<and>* (P -* P \<and>* R)) s"
  apply (clarsimp simp: sep_conj_def sep_impl_def septraction_def pred_neg_def)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x=y in exI)
  apply (clarsimp)
  apply (rule_tac x=x in exI)
  apply (clarsimp simp: sep_disj_commute)
  apply (rule_tac x=x in exI, clarsimp)
  by (metis sep_add_commute)




find_theorems hoare_triple new_rewards_and_penalties_context

lemma septractI_conj: "(\<And>s. Q s \<Longrightarrow> P s) \<Longrightarrow> (\<And>s h. s ## h \<Longrightarrow> P s \<Longrightarrow> \<exists>s'. Q s' \<and> s' ## h) \<Longrightarrow>  (P \<and>* R) s \<Longrightarrow> (P \<and>* (P -* Q \<and>* R)) s"
  apply (clarsimp simp: septraction_def sep_conj_def sep_impl_def pred_neg_def)
  sorry
  apply (rule sep_conj_impl[rotated, where Q="(not (P \<longrightarrow>* not (P \<and>* R)))"], assumption)
   apply (clarsimp simp: pred_neg_def)
   apply (erule notE)
   apply (sep_cancel)
  apply (sep_mp)
  apply (rule septract_cancel[rotated])
  apply (clarsimp simp: sep_conj_def sep_impl_def septraction_def pred_neg_def)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x=y in exI)
  apply (clarsimp)
  apply (rule_tac x=x in exI)
  apply (clarsimp simp: sep_disj_commute)
  apply (rule_tac x=x in exI)
  oops
  by (metis sep_add_commute)

lemma maps_to_mutual_disjoint: "maps_to l v s \<Longrightarrow> s ## h \<Longrightarrow> \<exists>s'. maps_to l v' s' \<and> s' ## h"
  by (metis maps_to_def maps_to_lens_pset' sep_disj_p_set_def)

lemma "\<forall>c P Q . (\<forall>x. hoare_triple (lift (P x \<and>* (EXS n. num_active_validators \<mapsto>\<^sub>l n))) (c x) Q) \<longrightarrow>
   (\<exists>P.  hoare_triple (lift P) (bindCont get_validator_churn_limit c) Q 
 \<and> (\<exists>P'. hoare_triple (lift P') (bindCont get_validator_churn_limit_fast c) (Q) \<and> ( P \<le> ((EXS n. num_active_validators \<mapsto>\<^sub>l n) \<and>* ((EXS n. num_active_validators \<mapsto>\<^sub>l n) -* P')))))" 
  apply (clarsimp)
  apply (rule exI)
  apply (intro conjI)
    apply (rule get_validator_churn_limit_spec')
  apply (erule_tac x=x in allE)
    apply (assumption)
  apply (rule exI)
  apply (intro conjI)
   apply (rule get_validator_churn_limit_fast_wp)
   apply (fastforce)
  apply (clarsimp)
  apply (sep_mp)
  apply (rule septractI_conj, blast)
    apply (clarsimp)
  apply (erule (1) maps_to_mutual_disjoint)

  apply (sep_cancel)+
  apply (blast)
  done

end
end