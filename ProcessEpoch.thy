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
    let old_previous_justified_checkpoint = previous_justified_checkpoint state;
    let old_current_justified_checkpoint = current_justified_checkpoint state;

    let state' = state \<lparr> current_justified_checkpoint := old_current_justified_checkpoint \<rparr>;
    None
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
      None
    }
  }"

end