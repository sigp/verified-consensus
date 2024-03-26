theory Invariants
  imports Main Types Unsigned Config HOL.Nat
begin

primrec var_list_len :: "'a VariableList \<Rightarrow> u64" where
  "var_list_len (VariableList l) = nat_to_u64 (length l)"

primrec var_list_inner :: "'a VariableList \<Rightarrow> 'a list" where
  "var_list_inner (VariableList l) = l"

definition valid_var_list :: "('a \<Rightarrow> bool) \<Rightarrow> u64 \<Rightarrow> 'a VariableList \<Rightarrow> bool" where
  "valid_var_list pred n l \<equiv>
    u64_to_nat (var_list_len l) \<le> u64_to_nat n \<and>
    list_all pred (var_list_inner l)"

(* TODO: delete, truncates *)
primrec vector_len :: "'a Vector \<Rightarrow> u64" where
  "vector_len (Vector l) = nat_to_u64 (length l)"

primrec vector_inner :: "'a Vector \<Rightarrow> 'a list" where
  "vector_inner (Vector l) = l"

definition valid_vector :: "('a \<Rightarrow> bool) \<Rightarrow> u64 \<Rightarrow> 'a Vector \<Rightarrow> bool" where
  "valid_vector pred n v \<equiv>
    length (vector_inner v) = u64_to_nat n \<and>
    list_all pred (vector_inner v)"

definition valid_hash256 :: "Hash256 \<Rightarrow> bool" where
  "valid_hash256 h \<equiv> case h of (Hash256 bytes) \<Rightarrow> length bytes = 32"

definition valid_public_key :: "PublicKey \<Rightarrow> bool" where
  "valid_public_key k \<equiv> case k of (PublicKey bytes) \<Rightarrow> length bytes = 96"

definition valid_version :: "Version \<Rightarrow> bool" where
  "valid_version v \<equiv> case v of (Version bytes) \<Rightarrow> length bytes = 4"

definition valid_fork :: "Fork \<Rightarrow> bool" where
  "valid_fork f \<equiv>
    valid_version (previous_version_f f) \<and>
    valid_version (current_version_f f)"

definition valid_beacon_block_header :: "BeaconBlockHeader \<Rightarrow> bool" where
  "valid_beacon_block_header header \<equiv>
    valid_hash256 (parent_root_f header) \<and>
    valid_hash256 (BeaconBlockHeader.state_root_f header) \<and>
    valid_hash256 (body_root_f header)"

definition valid_eth1_data :: "Eth1Data \<Rightarrow> bool" where
  "valid_eth1_data data \<equiv>
    valid_hash256 (deposit_root_f data) \<and>
    valid_hash256 (Eth1Data.block_hash_f data)"

definition valid_validator :: "Validator \<Rightarrow> bool" where
  "valid_validator v \<equiv>
    valid_public_key (pubkey_f v) \<and>
    valid_hash256 (withdrawal_credentials_f v)"

primrec bitvector_inner :: "Bitvector \<Rightarrow> bool list" where
  "bitvector_inner (Bitvector bools) = bools"

definition valid_bitvector :: "u64 \<Rightarrow> Bitvector \<Rightarrow> bool" where
  "valid_bitvector n v \<equiv> case v of Bitvector bools \<Rightarrow> length bools = u64_to_nat n"

definition valid_checkpoint :: "Checkpoint \<Rightarrow> bool" where
  "valid_checkpoint c \<equiv> valid_hash256 (Checkpoint.root_f c)"

definition valid_participation_flags :: "ParticipationFlags \<Rightarrow> bool" where
  "valid_participation_flags flags \<equiv>
    case flags of ParticipationFlags bools \<Rightarrow> length bools = 3"

definition valid_sync_committee :: "Config \<Rightarrow> SyncCommittee \<Rightarrow> bool" where
  "valid_sync_committee c sync_committee \<equiv>
    valid_vector valid_public_key (SYNC_COMMITTEE_SIZE c) (pubkeys_f sync_committee) \<and>
    valid_public_key (aggregate_pubkey_f sync_committee)"

definition option_field :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool" where
  "option_field f opt \<equiv> case opt of
    Some value \<Rightarrow> f value
    | None \<Rightarrow> True"

definition valid_beacon_state :: "Config \<Rightarrow> BeaconState \<Rightarrow> bool" where
  "valid_beacon_state c state \<equiv>
    option_field valid_hash256 (genesis_validators_root_f state) \<and>
    option_field valid_fork (fork_f state) \<and>
    option_field valid_beacon_block_header (latest_block_header_f state) \<and>
    option_field (valid_vector valid_hash256 (SLOTS_PER_HISTORICAL_ROOT c)) (block_roots_f state) \<and>
    option_field (valid_vector valid_hash256 (SLOTS_PER_HISTORICAL_ROOT c)) (state_roots_f state) \<and>
    option_field (valid_var_list valid_hash256 (HISTORICAL_ROOTS_LIMIT c)) (historical_roots_f state) \<and>
    option_field valid_eth1_data (eth1_data_f state) \<and>
    option_field (valid_var_list valid_eth1_data (SLOTS_PER_ETH1_VOTING_PERIOD c)) (eth1_data_votes_f state) \<and>
    option_field (valid_var_list valid_validator (VALIDATOR_REGISTRY_LIMIT c)) (validators_f state) \<and>
    option_field (valid_var_list (\<lambda>_. True) (VALIDATOR_REGISTRY_LIMIT c)) (balances_f state) \<and>
    option_field (valid_vector valid_hash256 (EPOCHS_PER_HISTORICAL_VECTOR c)) (randao_mixes_f state) \<and>
    option_field (valid_vector (\<lambda>_. True) (EPOCHS_PER_SLASHINGS_VECTOR c)) (slashings_f state) \<and>
    option_field (valid_var_list valid_participation_flags (VALIDATOR_REGISTRY_LIMIT c))
               (previous_epoch_participation_f state) \<and>
    option_field (valid_var_list valid_participation_flags (VALIDATOR_REGISTRY_LIMIT c))
               (current_epoch_participation_f state) \<and>
    option_field (valid_bitvector (JUSTIFICATION_BITS_LENGTH c)) (justification_bits_f state) \<and>
    option_field valid_checkpoint (previous_justified_checkpoint_f state) \<and>
    option_field valid_checkpoint (current_justified_checkpoint_f state) \<and>
    option_field valid_checkpoint (finalized_checkpoint_f state) \<and>
    option_field (valid_var_list (\<lambda>_. True) (VALIDATOR_REGISTRY_LIMIT c)) (inactivity_scores_f state) \<and>
    option_field (valid_sync_committee c) (current_sync_committee_f state) \<and>
    option_field (valid_sync_committee c) (next_sync_committee_f state)"

end