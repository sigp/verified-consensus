theory Helpers
  imports Utils Types Config Invariants "HOL-Library.Monad_Syntax"
begin

definition compute_start_slot_at_epoch :: "Config \<Rightarrow> Epoch \<Rightarrow> Slot" where
  "compute_start_slot_at_epoch c e \<equiv> Slot (the (epoch_to_u64 e .* SLOTS_PER_EPOCH c))"

definition get_current_epoch :: "Config \<Rightarrow> BeaconState \<Rightarrow> Epoch" where
  "get_current_epoch c state \<equiv>
    Epoch (the ((slot_to_u64 (slot_f state) \\ SLOTS_PER_EPOCH c)))"

definition get_previous_epoch :: "Config \<Rightarrow> BeaconState \<Rightarrow> Epoch" where
  "get_previous_epoch c state \<equiv>
    let current_epoch = get_current_epoch c state in
    if current_epoch = GENESIS_EPOCH then
      GENESIS_EPOCH
    else
      the (current_epoch .- Epoch (u64 1))"

definition is_active_validator :: "Validator \<Rightarrow> Epoch \<Rightarrow> bool" where
  "is_active_validator validator e \<equiv>
    activation_epoch_f validator \<le> e \<and> e < exit_epoch_f validator"

definition get_active_validator_indices :: "BeaconState \<Rightarrow> Epoch \<Rightarrow> u64 list" where
  "get_active_validator_indices state e \<equiv>
    [i. (i, v) \<leftarrow> enumerate (list_inner (validators_f state)), is_active_validator v e]"

definition get_eligible_validator_indices :: "Config \<Rightarrow> BeaconState \<Rightarrow> (u64 list) option" where
  "get_eligible_validator_indices c state \<equiv> do {
    let previous_epoch = get_previous_epoch c state;
    previous_epoch_p1 \<leftarrow> previous_epoch .+ Epoch (u64 1);
    Some [i. (i, v) \<leftarrow> enumerate (list_inner (validators_f state)),
          is_active_validator v previous_epoch \<or>
            (slashed_f v \<and> previous_epoch_p1 < withdrawable_epoch_f v)]
  }"

definition has_flag :: "ParticipationFlags \<Rightarrow> nat \<Rightarrow> bool" where
  "has_flag flags flag_index \<equiv>
    case flags of ParticipationFlags bools \<Rightarrow> bools ! flag_index"

definition get_unslashed_participating_indices ::
   "Config \<Rightarrow> BeaconState \<Rightarrow> nat \<Rightarrow> Epoch \<Rightarrow> (u64 set) option"
where
  "get_unslashed_participating_indices c state flag_index e \<equiv> do {
    let previous_epoch = get_previous_epoch c state;
    let current_epoch = get_current_epoch c state;
    _ \<leftarrow> assert (e = previous_epoch \<or> e = current_epoch);
    let epoch_participation = (if e = current_epoch then
      current_epoch_participation_f state
    else
      previous_epoch_participation_f state);
    let active_validator_indices = get_active_validator_indices state e;
    let participating_indices = [
      i.
      i \<leftarrow> active_validator_indices,
      has_flag (unsafe_list_index epoch_participation i) flag_index
    ];
    Some (
      set (
        filter (\<lambda>index. \<not> slashed_f (unsafe_list_index (validators_f state) index))
               participating_indices))
  }"

definition get_total_balance :: "Config \<Rightarrow> BeaconState \<Rightarrow> u64 set \<Rightarrow> u64 option" where
  "get_total_balance c state indices \<equiv> do {
    total \<leftarrow> safe_sum ((\<lambda>i. effective_balance_f (unsafe_list_index (validators_f state) i)) ` indices);
    Some (max (EFFECTIVE_BALANCE_INCREMENT c) total)
  }"

definition get_total_active_balance :: "Config \<Rightarrow> BeaconState \<Rightarrow> u64 option" where
  "get_total_active_balance c state \<equiv>
    get_total_balance c state
                      (set (get_active_validator_indices state (get_current_epoch c state)))"

definition get_block_root_at_slot :: "Config \<Rightarrow> BeaconState \<Rightarrow> Slot \<Rightarrow> Hash256 option" where
  "get_block_root_at_slot c state slot \<equiv> do {
    upper_limit \<leftarrow> slot .+ Slot (SLOTS_PER_HISTORICAL_ROOT c);
    _ \<leftarrow> assert (slot < slot_f state \<and> slot_f state \<le> upper_limit);
    i \<leftarrow> slot_to_u64 slot .% SLOTS_PER_HISTORICAL_ROOT c;
    vector_index (block_roots_f state) i
  }"

definition get_block_root :: "Config \<Rightarrow> BeaconState \<Rightarrow> Epoch \<Rightarrow> Hash256 option" where
  "get_block_root c state epoch \<equiv>
    get_block_root_at_slot c state (compute_start_slot_at_epoch c epoch)"

end