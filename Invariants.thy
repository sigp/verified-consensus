theory Invariants
  imports Main Types Unsigned Config HOL.Nat
begin

primrec list_len :: "'a List \<Rightarrow> u64" where
  "list_len (List l) = u64 (length l)"

primrec list_inner :: "'a List \<Rightarrow> 'a list" where
  "list_inner (List l) = l"

definition valid_list :: "('a \<Rightarrow> bool) \<Rightarrow> u64 \<Rightarrow> 'a List \<Rightarrow> bool" where
  "valid_list pred n l \<equiv>
    valid_u64 n \<and>
    u64_to_nat (list_len l) \<le> u64_to_nat n \<and>
    list_all pred (list_inner l)"

primrec vector_len :: "'a Vector \<Rightarrow> u64" where
  "vector_len (Vector l) = u64 (length l)"

primrec vector_inner :: "'a Vector \<Rightarrow> 'a list" where
  "vector_inner (Vector l) = l"

definition valid_vector :: "('a \<Rightarrow> bool) \<Rightarrow> u64 \<Rightarrow> 'a Vector \<Rightarrow> bool" where
  "valid_vector pred n v \<equiv>
    valid_u64 n \<and>
    u64_to_nat (vector_len v) = u64_to_nat n \<and>
    list_all pred (vector_inner v)"

definition valid_hash256 :: "Hash256 \<Rightarrow> bool" where
  "valid_hash256 h \<equiv> case h of (Hash256 bytes) \<Rightarrow> length bytes = 32"

definition valid_public_key :: "PublicKey \<Rightarrow> bool" where
  "valid_public_key k \<equiv> case k of (PublicKey bytes) \<Rightarrow> length bytes = 96"

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

definition valid_eth1_data :: "Eth1Data \<Rightarrow> bool" where
  "valid_eth1_data data \<equiv>
    valid_hash256 (deposit_root data) \<and>
    valid_u64 (deposit_count data) \<and>
    valid_hash256 (block_hash data)"

definition valid_validator :: "Validator \<Rightarrow> bool" where
  "valid_validator v \<equiv>
    valid_public_key (pubkey v) \<and>
    valid_hash256 (withdrawal_credentials v) \<and>
    valid_u64 (effective_balance v) \<and>
    valid_epoch (activation_eligibility_epoch v) \<and>
    valid_epoch (activation_epoch v) \<and>
    valid_epoch (exit_epoch v) \<and>
    valid_epoch (withdrawable_epoch v)"

definition valid_bitvector :: "u64 \<Rightarrow> Bitvector \<Rightarrow> bool" where
  "valid_bitvector n v \<equiv> case v of Bitvector bools \<Rightarrow> length bools = u64_to_nat n"

definition valid_checkpoint :: "Checkpoint \<Rightarrow> bool" where
  "valid_checkpoint c \<equiv> valid_epoch (Checkpoint.epoch c) \<and> valid_hash256 (Checkpoint.root c)"

definition valid_participation_flags :: "ParticipationFlags \<Rightarrow> bool" where
  "valid_participation_flags flags \<equiv>
    case flags of ParticipationFlags bools \<Rightarrow> length bools = 3"

definition valid_sync_committee :: "Config \<Rightarrow> SyncCommittee \<Rightarrow> bool" where
  "valid_sync_committee c sync_committee \<equiv>
    valid_vector valid_public_key (SYNC_COMMITTEE_SIZE c) (pubkeys sync_committee) \<and>
    valid_public_key (aggregate_pubkey sync_committee)"

definition valid_beacon_state :: "Config \<Rightarrow> BeaconState \<Rightarrow> bool" where
  "valid_beacon_state c state \<equiv>
    valid_u64 (genesis_time state) \<and>
    valid_hash256 (genesis_validators_root state) \<and>
    valid_slot (slot state) \<and>
    valid_fork (fork state) \<and>
    valid_beacon_block_header (latest_block_header state) \<and>
    valid_vector valid_hash256 (SLOTS_PER_HISTORICAL_ROOT c) (block_roots state) \<and>
    valid_vector valid_hash256 (SLOTS_PER_HISTORICAL_ROOT c) (state_roots state) \<and>
    valid_list valid_hash256 (HISTORICAL_ROOTS_LIMIT c) (historical_roots state) \<and>
    valid_eth1_data (eth1_data state) \<and>
    valid_list valid_eth1_data (SLOTS_PER_ETH1_VOTING_PERIOD c) (eth1_data_votes state) \<and>
    valid_u64 (eth1_deposit_index state) \<and>
    valid_list valid_validator (VALIDATOR_REGISTRY_LIMIT c) (validators state) \<and>
    valid_list valid_u64 (VALIDATOR_REGISTRY_LIMIT c) (balances state) \<and>
    valid_vector valid_hash256 (EPOCHS_PER_HISTORICAL_VECTOR c) (randao_mixes state) \<and>
    valid_vector valid_u64 (EPOCHS_PER_SLASHINGS_VECTOR c) (slashings state) \<and>
    valid_list valid_participation_flags (VALIDATOR_REGISTRY_LIMIT c)
               (previous_epoch_participation state) \<and>
    valid_list valid_participation_flags (VALIDATOR_REGISTRY_LIMIT c)
               (current_epoch_participation state) \<and>
    valid_bitvector (JUSTIFICATION_BITS_LENGTH c) (justification_bits state) \<and>
    valid_checkpoint (previous_justified_checkpoint state) \<and>
    valid_checkpoint (current_justified_checkpoint state) \<and>
    valid_checkpoint (finalized_checkpoint state) \<and>
    valid_list valid_u64 (VALIDATOR_REGISTRY_LIMIT c) (inactivity_scores state) \<and>
    valid_sync_committee c (current_sync_committee state) \<and>
    valid_sync_committee c (next_sync_committee state)"

end