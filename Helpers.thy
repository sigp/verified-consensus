theory Helpers
  imports Utils Types Config Invariants "HOL-Library.Monad_Syntax"
begin

context verified_con
begin

definition compute_start_slot_at_epoch :: "Config \<Rightarrow> Epoch \<Rightarrow> Slot" where
  "compute_start_slot_at_epoch c e \<equiv> Slot (epoch_to_u64 e * SLOTS_PER_EPOCH c)"

definition slot_to_epoch :: "Config \<Rightarrow> Slot \<Rightarrow> Epoch" where
  "slot_to_epoch c slot \<equiv>
    Epoch (slot_to_u64 slot div SLOTS_PER_EPOCH c)"

definition get_current_epoch :: "(Epoch, 'a) cont " where
  "get_current_epoch \<equiv> do {
    slot \<leftarrow> read beacon_slots;
    return (slot_to_epoch config slot)
   }"

definition get_previous_epoch :: "(Epoch, 'a) cont" where
  "get_previous_epoch \<equiv> do {
    current_epoch \<leftarrow> get_current_epoch;
    if current_epoch = GENESIS_EPOCH then
      return GENESIS_EPOCH
    else
      current_epoch .- Epoch 1
  }"

definition is_active_validator :: "Validator \<Rightarrow> Epoch \<Rightarrow> bool" where
  "is_active_validator validator e \<equiv>
    activation_epoch_f validator \<le> e \<and> e < exit_epoch_f validator"

definition active_validator_indices :: "Epoch \<Rightarrow> Validator VariableList \<Rightarrow> u64 list" where
  "active_validator_indices e vs \<equiv>
    [i. (i, v) \<leftarrow> enumerate (var_list_inner vs), is_active_validator v e]"

definition get_active_validator_indices :: "Epoch \<Rightarrow> (u64 list, 'a) cont" where
  "get_active_validator_indices e \<equiv> liftM (active_validator_indices e) (read validators)"

definition eligible_validator_indices :: "Epoch \<Rightarrow> Epoch \<Rightarrow> Validator VariableList \<Rightarrow> u64 list" where
  "eligible_validator_indices previous_epoch previous_epoch_plus_1 vs \<equiv>
    [i. (i, v) \<leftarrow> enumerate (var_list_inner vs),
       is_active_validator v previous_epoch \<or>
         (slashed_f v \<and> previous_epoch_plus_1 < withdrawable_epoch_f v)]"

definition get_eligible_validator_indices :: "(u64 list, 'a) cont" where
  "get_eligible_validator_indices \<equiv> do {
    previous_epoch \<leftarrow> get_previous_epoch;
    previous_epoch_p1 \<leftarrow> previous_epoch .+ Epoch 1;
    liftM (eligible_validator_indices previous_epoch previous_epoch_p1) (read validators)
  }"

definition has_flag :: "ParticipationFlags \<Rightarrow> nat \<Rightarrow> bool" where
  "has_flag flags flag_index \<equiv>
    case flags of ParticipationFlags bools \<Rightarrow> bools ! flag_index"

definition get_unslashed_participating_indices ::
   "nat \<Rightarrow> Epoch \<Rightarrow> (u64 set, 'a) cont"
where
  "get_unslashed_participating_indices flag_index e \<equiv> do {
    previous_epoch <- get_previous_epoch;
    current_epoch <- get_current_epoch;
    _ \<leftarrow> assertion (\<lambda>_. e = previous_epoch \<or> e = current_epoch);
    epoch_participation <- (if e = current_epoch then read current_epoch_participation
                                                 else read previous_epoch_participation);
    active_validator_indices <- get_active_validator_indices e;
    let participating_indices = [
      i.
      i \<leftarrow> active_validator_indices,
      has_flag (unsafe_var_list_index epoch_participation i) flag_index
    ];
    v <- read validators;
    return (
      list.set (
        filter (\<lambda>index. \<not> slashed_f (unsafe_var_list_index v index))
               participating_indices))
  }"

definition get_total_balance :: " u64 set \<Rightarrow> (u64, 'a) cont" where
  "get_total_balance indices \<equiv> do {
    v <- read validators;
    total \<leftarrow> safe_sum ((\<lambda>i. effective_balance_f (unsafe_var_list_index (v) i)) ` indices);
    return (max (EFFECTIVE_BALANCE_INCREMENT config) total)
  }"

definition get_total_active_balance :: "(u64, 'a) cont" where
  "get_total_active_balance  \<equiv> do {
   current_epoch <- get_current_epoch;
   inds <- get_active_validator_indices current_epoch;
   get_total_balance (list.set inds)}"

definition get_block_root_at_slot :: "Slot \<Rightarrow> (Hash256, 'a) cont" where
  "get_block_root_at_slot slot \<equiv> do {
    upper_limit \<leftarrow> slot .+ Slot (SLOTS_PER_HISTORICAL_ROOT config);
    state_slot <- read beacon_slots;
    _ <- assertion (\<lambda>_. slot < state_slot \<and> state_slot \<le> upper_limit);
    i \<leftarrow> slot_to_u64 slot .% SLOTS_PER_HISTORICAL_ROOT config;
    b \<leftarrow> read block_roots;
    lift_option (vector_index b i)
  }"

definition get_block_root :: " Epoch \<Rightarrow> (Hash256, 'a) cont" where
  "get_block_root epoch \<equiv>
    get_block_root_at_slot (compute_start_slot_at_epoch config epoch)"

definition get_base_reward_per_increment :: " (u64, 'a) cont" where
  "get_base_reward_per_increment \<equiv> do {
    total_active_balance \<leftarrow> get_total_active_balance;
    sqrt_total_active_balance \<leftarrow> integer_squareroot total_active_balance;
    x <- EFFECTIVE_BALANCE_INCREMENT config .* BASE_REWARD_FACTOR config;
    sqrt_total_active_balance \\ x
  }"

definition get_base_reward :: " u64 \<Rightarrow> (u64, 'a) cont" where
  "get_base_reward index \<equiv> do {
    v <- read validators;
    validator \<leftarrow> lift_option (var_list_index v index);
    increments \<leftarrow> effective_balance_f validator \\ EFFECTIVE_BALANCE_INCREMENT config;
    base_reward_per_increment \<leftarrow> get_base_reward_per_increment;
    increments .* base_reward_per_increment
  }"

definition get_finality_delay :: "(u64, 'a) cont" where
  "get_finality_delay \<equiv> do {
    previous_epoch <- get_previous_epoch;
    final <- read finalized_checkpoint;
    epoch_to_u64 previous_epoch .- epoch_to_u64 (epoch_f final)}"

definition is_in_inactivity_leak :: "(bool, 'a) cont" where
  "is_in_inactivity_leak \<equiv> do {
    finality_delay \<leftarrow> get_finality_delay;
    return (finality_delay > MIN_EPOCHS_TO_INACTIVITY_PENALTY config)
  }"

end
end