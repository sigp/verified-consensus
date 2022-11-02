theory Helpers
  imports Utils Types Config Invariants "HOL-Library.Monad_Syntax"
begin

definition get_current_epoch :: "Config \<Rightarrow> BeaconState \<Rightarrow> Epoch" where
  "get_current_epoch c state \<equiv>
    Epoch (the ((slot_to_u64 (slot state) \\ SLOTS_PER_EPOCH c)))"

definition get_previous_epoch :: "Config \<Rightarrow> BeaconState \<Rightarrow> Epoch" where
  "get_previous_epoch c state \<equiv>
    let current_epoch = get_current_epoch c state in
    if current_epoch = GENESIS_EPOCH then
      GENESIS_EPOCH
    else
      the (current_epoch .- Epoch (u64 1))"

definition is_active_validator :: "Validator \<Rightarrow> Epoch \<Rightarrow> bool" where
  "is_active_validator validator e \<equiv>
    activation_epoch validator \<le> e \<and> e < exit_epoch validator"

definition get_active_validator_indices :: "BeaconState \<Rightarrow> Epoch \<Rightarrow> u64 list" where
  "get_active_validator_indices state e \<equiv>
    [i. (i, v) \<leftarrow> enumerate (list_inner (validators state)), is_active_validator v e]"

definition has_flag :: "ParticipationFlags \<Rightarrow> nat \<Rightarrow> bool" where
  "has_flag flags flag_index \<equiv>
    case flags of ParticipationFlags bools \<Rightarrow> bools ! flag_index"

(* FIXME(sproul): cleaner indexing without `list_inner` *)
definition get_unslashed_participating_indices ::
   "Config \<Rightarrow> BeaconState \<Rightarrow> nat \<Rightarrow> Epoch \<Rightarrow> (u64 set) option"
where
  "get_unslashed_participating_indices c state flag_index e \<equiv> do {
    let previous_epoch = get_previous_epoch c state;
    let current_epoch = get_current_epoch c state;
    _ \<leftarrow> assert (e = previous_epoch \<or> e = current_epoch);
    let epoch_participation = (if e = current_epoch then
      current_epoch_participation state
    else
      previous_epoch_participation state);
    let active_validator_indices = get_active_validator_indices state e;
    let participating_indices = [
      i.
      i \<leftarrow> active_validator_indices,
      has_flag (list_inner epoch_participation ! u64_to_nat i) flag_index
    ];
    Some (
      set (
        filter (\<lambda>index. \<not> slashed (list_inner (validators state) ! u64_to_nat index))
               participating_indices))
  }"

end