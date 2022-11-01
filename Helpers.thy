theory Helpers
  imports Types Config Invariants "HOL-Library.Monad_Syntax"
begin

definition get_current_epoch :: "Config \<Rightarrow> BeaconState \<Rightarrow> Epoch option" where
  "get_current_epoch c state \<equiv>
    map_option Epoch (slot_to_u64 (slot state) \\ SLOTS_PER_EPOCH c)"

definition get_previous_epoch :: "Config \<Rightarrow> BeaconState \<Rightarrow> Epoch option" where
  "get_previous_epoch c state \<equiv> do {
    current_epoch \<leftarrow> get_current_epoch c state;
    if current_epoch = GENESIS_EPOCH then
      Some GENESIS_EPOCH
    else
      current_epoch .- Epoch (u64 1)
  }"

end