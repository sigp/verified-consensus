theory ProcessEpoch
  imports Types Invariants Helpers Main "HOL-Library.Monad_Syntax"
begin

definition weigh_justification_and_finalization ::
  "Config \<Rightarrow> BeaconState \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> BeaconState option"
where
  "weigh_justification_and_finalization c state
                                        total_active_balance
                                        previous_epoch_target_balance
                                        current_epoch_target_balance \<equiv> do {
    let previous_epoch = get_previous_epoch c state;
    let current_epoch = get_current_epoch c state;
    let old_previous_justified_checkpoint = previous_justified_checkpoint_f state;
    let old_current_justified_checkpoint = current_justified_checkpoint_f state;

    let state = state \<lparr> current_justified_checkpoint_f := old_current_justified_checkpoint \<rparr>;
    let shifted_justification_bits = shift_and_clear_bitvector c (justification_bits_f state);
    let state = state \<lparr> justification_bits_f := shifted_justification_bits \<rparr>;
    previous_epoch_target_x3 \<leftarrow> previous_epoch_target_balance .* u64 3;
    current_epoch_target_x3 \<leftarrow> current_epoch_target_balance .* u64 3;
    total_active_balance_x2 \<leftarrow> total_active_balance .* u64 2;
    state \<leftarrow> if previous_epoch_target_x3 \<ge> total_active_balance_x2 then do {
        let updated_justification_bits = bitvector_update (justification_bits_f state) 1 False;
        block_root \<leftarrow> get_block_root c state previous_epoch;
        Some (state \<lparr>
          current_justified_checkpoint_f := \<lparr> epoch_f = previous_epoch, root_f = block_root \<rparr>,
          justification_bits_f := updated_justification_bits
        \<rparr>)
      } else Some state;
     state \<leftarrow> if current_epoch_target_x3 \<ge> total_active_balance_x2 then do {
        let updated_justification_bits = bitvector_update (justification_bits_f state) 0 False;
        block_root \<leftarrow> get_block_root c state current_epoch;
        Some (state \<lparr>
          current_justified_checkpoint_f := \<lparr> epoch_f = current_epoch, root_f = block_root \<rparr>,
          justification_bits_f := updated_justification_bits
        \<rparr>)
      } else Some state;

    let bits = justification_bits_f state;

    let state = (
      if bitvector_all bits 1 4 \<and>
         the (epoch_f old_previous_justified_checkpoint .+ Epoch (u64 3)) = current_epoch
      then
        state \<lparr> finalized_checkpoint_f := old_previous_justified_checkpoint \<rparr>
      else state
    );
    let state = (
      if bitvector_all bits 1 3 \<and>
         the (epoch_f old_previous_justified_checkpoint .+ Epoch (u64 2)) = current_epoch
      then
        state \<lparr> finalized_checkpoint_f := old_previous_justified_checkpoint \<rparr>
      else state
    );
    let state = (
      if bitvector_all bits 0 3 \<and>
         the (epoch_f old_current_justified_checkpoint .+ Epoch (u64 2)) = current_epoch
      then
        state \<lparr> finalized_checkpoint_f := old_current_justified_checkpoint \<rparr>
      else state
    );
    let state = (
      if bitvector_all bits 0 2 \<and>
         the (epoch_f old_current_justified_checkpoint .+ Epoch (u64 1)) = current_epoch
      then
        state \<lparr> finalized_checkpoint_f := old_current_justified_checkpoint \<rparr>
      else state
    );
    Some state
  }"

definition process_justification_and_finalization ::
  "Config \<Rightarrow> BeaconState \<Rightarrow> BeaconState option"
where
  "process_justification_and_finalization c state \<equiv> do {
    let previous_epoch = get_previous_epoch c state;
    let current_epoch = get_current_epoch c state;
    epoch1 \<leftarrow> GENESIS_EPOCH .+ Epoch (u64 1);
    if current_epoch \<le> epoch1 then
      Some state
    else do {
      previous_indices \<leftarrow> 
        get_unslashed_participating_indices c state TIMELY_TARGET_FLAG_INDEX previous_epoch;
      current_indices \<leftarrow>
        get_unslashed_participating_indices c state TIMELY_TARGET_FLAG_INDEX current_epoch;
      total_active_balance \<leftarrow> get_total_active_balance c state;
      previous_target_balance \<leftarrow> get_total_balance c state previous_indices;
      current_target_balance \<leftarrow> get_total_balance c state previous_indices;
      weigh_justification_and_finalization
        c state total_active_balance previous_target_balance current_target_balance
    }
  }"

definition get_flag_index_deltas ::
  "Config \<Rightarrow> BeaconState \<Rightarrow> nat \<Rightarrow> (u64 list \<times> u64 list) option"
where
  "get_flag_index_deltas c state flag_index \<equiv> do {
    let init_rewards = [u64 0. _ \<leftarrow> [0..<length (list_inner (validators_f state))]];
    let init_penalties = init_rewards;
    let previous_epoch = get_previous_epoch c state;
    unslashed_participating_indices \<leftarrow> get_unslashed_participating_indices c state flag_index
                                                                           previous_epoch;
    let weight = PARTICIPATION_FLAG_WEIGHTS ! flag_index;
    unslashed_participating_balance \<leftarrow> get_total_balance c state unslashed_participating_indices;
    unslashed_participating_increments \<leftarrow> unslashed_participating_balance \\
                                            EFFECTIVE_BALANCE_INCREMENT c;
    total_active_balance \<leftarrow> get_total_active_balance c state;
    active_increments \<leftarrow> total_active_balance \\ EFFECTIVE_BALANCE_INCREMENT c;
    eligible_validator_indices \<leftarrow> get_eligible_validator_indices c state;
    foldl (\<lambda>opt index. do {
      (rewards, penalties) \<leftarrow> opt;
      base_reward \<leftarrow> get_base_reward c state index;
      in_inactivity_leak \<leftarrow> is_in_inactivity_leak c state;
      let index_nat = u64_to_nat index;
      if index \<in> unslashed_participating_indices then (
        if \<not> in_inactivity_leak then do {
          reward_numerator \<leftarrow> base_reward .* weight \<bind> flip (.*) unslashed_participating_increments;
          reward_denominator \<leftarrow> active_increments .* WEIGHT_DENOMINATOR;
          reward \<leftarrow> reward_numerator \\ reward_denominator;
          total_reward \<leftarrow> rewards ! index_nat .+ reward;
          let rewards' = list_update rewards index_nat total_reward;
          Some (rewards', penalties)
        } else do {
          Some (rewards, penalties)
        }
      ) else if flag_index \<noteq> TIMELY_HEAD_FLAG_INDEX then do {
        penalty \<leftarrow> base_reward .* weight \<bind> (flip (\\) WEIGHT_DENOMINATOR);
        total_penalty \<leftarrow> penalties ! index_nat .+ penalty;
        let penalties' = list_update penalties index_nat total_penalty;
        Some (rewards, penalties')
      } else (
        Some (rewards, penalties)
      )
    }) (Some (init_rewards, init_penalties)) eligible_validator_indices
  }"

definition process_rewards_and_penalties ::
  "Config \<Rightarrow> BeaconState \<Rightarrow> BeaconState option"
where
  "process_rewards_and_penalties c state \<equiv>
    if get_current_epoch c state = GENESIS_EPOCH then
      Some state else do {
    None
  }"

end