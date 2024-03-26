theory JustificationAndFinalizationProof                                
  imports Hoare_Logic
begin

context hoare_logic
begin

type_synonym 'var State = "BeaconState \<times> (('var, 'var heap_value) heap)"

(*
definition weigh_justification_and_finalization ::
  "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
where
  "weigh_justification_and_finalization total_active_balance
                                        previous_epoch_target_balance
                                        current_epoch_target_balance \<equiv> do {
     previous_epoch <- get_previous_epoch;
     current_epoch  <- get_current_epoch;
     old_previous_justified_checkpoint <- read previous_justified_checkpoint;
     old_current_justified_checkpoint  <- read current_justified_checkpoint;
     _ <- (current_justified_checkpoint ::= old_current_justified_checkpoint);
     bits <- read justification_bits;
     let shifted_justification_bits = shift_and_clear_bitvector config bits;
     _ <- (justification_bits ::= shifted_justification_bits);
     previous_epoch_target_x3 \<leftarrow> previous_epoch_target_balance .* 3;
     current_epoch_target_x3  \<leftarrow> current_epoch_target_balance .* 3;
     total_active_balance_x2  \<leftarrow> total_active_balance .* 2;
     when (previous_epoch_target_x3 \<ge> total_active_balance_x2)
      (do {bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 1 False;
           block_root <- get_block_root previous_epoch;
           _  <- (current_justified_checkpoint ::= current_justified_checkpoint\<lparr>epoch_f := previous_epoch, root_f := block_root\<rparr>);
          (justification_bits ::= updated_justification_bits)});
     when (current_epoch_target_x3 \<ge> total_active_balance_x2) 
      (do {bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 0 False;
           block_root <- get_block_root previous_epoch;
           _ <- (current_justified_checkpoint ::= current_justified_checkpoint\<lparr>epoch_f := current_epoch, root_f := block_root\<rparr>);
          (justification_bits ::= updated_justification_bits)});
     bits <- read justification_bits;
     x <- epoch_f old_previous_justified_checkpoint .+ Epoch 3;
     _ <- (if (bitvector_all bits 1 4 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ()); 
     x <- epoch_f old_previous_justified_checkpoint .+ Epoch 2;
     _ <- (if (bitvector_all bits 1 3 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ());
     _ <- (if (bitvector_all bits 0 3 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ());
     (if (bitvector_all bits 0 2 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ())  
     }"

definition process_justification_and_finalization_pre ::
  "Slot \<Rightarrow> Checkpoint \<Rightarrow> Checkpoint \<Rightarrow> 'var State \<Rightarrow> bool"
  where
  "process_justification_and_finalization_pre
    slot
    old_previous_justified_checkpoint
    old_current_justified_checkpoint
    old_justification_bits \<equiv>
    maps_to beacon_slots slot \<and>*
    maps_to previous_justified_checkpoint old_previous_justified_checkpoint \<and>*
    maps_to current_justified_checkpoint old_current_justified_checkpoint \<and>*
    maps_to justification_bits old_justification_bits"

definition process_justification_and_finalization_post ::
  "BeaconState \<Rightarrow> bool"
where
  "process_justification_and_finalization_post state \<equiv> do {
     previous_epoch <- get_previous_epoch;
     current_epoch <- get_current_epoch;
     epoch1 \<leftarrow> GENESIS_EPOCH .+ Epoch 1;
    if current_epoch \<le> epoch1 then
      return ()
    else do {
      previous_indices \<leftarrow> 
        get_unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX previous_epoch;
      current_indices \<leftarrow>
        get_unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX current_epoch;
      total_active_balance    \<leftarrow> get_total_active_balance;
      previous_target_balance \<leftarrow> get_total_balance  previous_indices;
      current_target_balance  \<leftarrow> get_total_balance  previous_indices;
      weigh_justification_and_finalization
         total_active_balance previous_target_balance current_target_balance
    }
  }"
*)
(*
definition get_block_root_at_slot :: "Slot \<Rightarrow> (Hash256, 'a) cont" where
  "get_block_root_at_slot slot \<equiv> do {
    upper_limit \<leftarrow> slot .+ Slot (SLOTS_PER_HISTORICAL_ROOT config);
    state_slot <- read beacon_slots;
    (* state_slot - LENGTH \<le> slot *)
    (* state_slot - LENGTH..state_slot *)
    _ <- assertion (\<lambda>_. slot < state_slot \<and> state_slot \<le> upper_limit);
    i \<leftarrow> slot_to_u64 slot .% SLOTS_PER_HISTORICAL_ROOT config;
    b \<leftarrow> read block_roots;
    lift_option (vector_index b i)
  }"

definition get_block_root :: " Epoch \<Rightarrow> (Hash256, 'a) cont" where
  "get_block_root epoch \<equiv>
    get_block_root_at_slot (compute_start_slot_at_epoch config epoch)"
*)

definition get_block_root_at_slot_pre :: "Slot \<Rightarrow> Hash256 \<Rightarrow> Slot \<Rightarrow> Hash256 Vector \<Rightarrow> 'var State \<Rightarrow> bool" where
  "get_block_root_at_slot_pre slot slot_block_root current_slot block_roots_vec state \<equiv>
    slot < current_slot \<and>
    current_slot \<le> slot + Slot (SLOTS_PER_HISTORICAL_ROOT config) \<and>
    slot_to_u64 slot \<le> maxBound - SLOTS_PER_HISTORICAL_ROOT config \<and>
    SLOTS_PER_HISTORICAL_ROOT config \<noteq> 0 \<and>
    valid_vector valid_hash256 (SLOTS_PER_HISTORICAL_ROOT config) block_roots_vec \<and>
    vector_inner block_roots_vec ! u64_to_nat (slot_to_u64 slot mod SLOTS_PER_HISTORICAL_ROOT config) = slot_block_root \<and>
    (maps_to block_roots block_roots_vec \<and>*
     maps_to beacon_slots current_slot) state"

lemma length_vector_inner[simp]: "length (vector_inner (Vector v)) = length v"
  by (fastforce simp: vector_inner_def)

lemma get_block_root_at_slot_proof:
  "\<lblot>get_block_root_at_slot_pre slot slot_block_root current_slot block_roots_vec \<and>* R\<rblot>
   get_block_root_at_slot slot
   \<lblot>get_block_root_at_slot_pre slot slot_block_root current_slot block_roots_vec \<and>* R\<rblot>"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp: get_block_root_at_slot_def)
   apply wp
  apply clarsimp
  apply safe
   apply (unfold get_block_root_at_slot_pre_def)
   apply (clarsimp simp: plus_Slot_def less_eq_Slot_def)
   apply (erule plus_minus_no_overflow_ab)
   apply fastforce
  apply clarsimp
  apply sep_cancel+
  apply safe
  apply sep_cancel+
  apply safe
   apply (clarsimp simp: valid_vector_def)
   apply (case_tac block_roots_vec)
   apply clarsimp
   apply (simp add: unat_less_helper word_mod_less_divisor word_neq_0_conv)
  apply (case_tac block_roots_vec)
  apply (clarsimp simp: valid_vector_def)
  apply (rule unat_lt2p[where 'a=64, simplified])
  done

end
end