theory Invariants
  imports Main Types HOL.Nat
begin

primrec u64_to_nat :: "u64 \<Rightarrow> nat" where
  "u64_to_nat (u64 n) = n"

definition valid_u64 :: "u64 \<Rightarrow> bool" where
  "valid_u64 n \<equiv> u64_to_nat n < 2 ^ 64"

primrec list_len :: "'a List \<Rightarrow> u64" where
  "list_len (List l) = u64 (length l)"

definition valid_list :: "u64 \<Rightarrow> 'a List \<Rightarrow> bool" where
  "valid_list n l \<equiv> valid_u64 n \<and> u64_to_nat (list_len l) \<le> u64_to_nat n"

primrec vector_len :: "'a Vector \<Rightarrow> u64" where
  "vector_len (Vector l) = u64 (length l)"

definition valid_vector :: "u64 \<Rightarrow> 'a Vector \<Rightarrow> bool" where
  "valid_vector n v \<equiv> valid_u64 n \<and> u64_to_nat (vector_len v) = u64_to_nat n"

primrec slot_to_u64 :: "Slot \<Rightarrow> u64" where
  "slot_to_u64 (Slot n) = n"

definition valid_slot :: "Slot \<Rightarrow> bool" where
  "valid_slot s \<equiv> valid_u64 (slot_to_u64 s)"

primrec epoch_to_u64 :: "Epoch \<Rightarrow> u64" where
  "epoch_to_u64 (Epoch n) = n"

definition valid_epoch :: "Epoch \<Rightarrow> bool" where
  "valid_epoch e \<equiv> valid_u64 (epoch_to_u64 e)"

definition valid_hash256 :: "Hash256 \<Rightarrow> bool" where
  "valid_hash256 h \<equiv> case h of (Hash256 bytes) \<Rightarrow> length bytes = 32"

definition valid_version :: "Version \<Rightarrow> bool" where
  "valid_version v \<equiv> case v of (Version bytes) \<Rightarrow> length bytes = 4"

definition valid_fork :: "Fork \<Rightarrow> bool" where
  "valid_fork f \<equiv>
    valid_version (previous_version f) \<and>
    valid_version (current_version f) \<and>
    valid_epoch (Fork.epoch f)"

definition valid_beacon_block_header :: "BeaconBlockHeader \<Rightarrow> bool" where
  "valid_beacon_block_header header \<equiv>
    valid_slot (BeaconBlockHeader.slot header) \<and>
    valid_u64 (proposer_index header) \<and>
    valid_hash256 (parent_root header) \<and>
    valid_hash256 (state_root header) \<and>
    valid_hash256 (body_root header)"

definition valid_beacon_state :: "BeaconState \<Rightarrow> bool" where
  "valid_beacon_state state \<equiv>
    valid_u64 (genesis_time state) \<and>
    valid_hash256 (genesis_validators_root state) \<and>
    valid_slot (slot state) \<and>
    valid_fork (fork state) \<and>
    valid_beacon_block_header (latest_block_header state)"
end