theory Types
  imports Main Unsigned
begin

(*
 * We use names ending in _f for all record fields to prevent the unadorned name becoming
 * unusable. See: https://isabelle.in.tum.de/dist/library/Doc/Tutorial/Records.html
*)

datatype Hash256 = Hash256 "u8 list"
datatype 'a Vector = Vector "'a list"
datatype 'a List = List "'a list"

datatype Bitvector = Bitvector "bool list"

datatype PublicKey = PublicKey "u8 list"

datatype Version = Version "u8 list"

record Fork =
  previous_version_f :: Version
  current_version_f :: Version
  epoch_f :: Epoch

record BeaconBlockHeader =
  slot_f :: Slot
  proposer_index_f :: u64
  parent_root_f :: Hash256
  state_root_f :: Hash256
  body_root_f :: Hash256

record Eth1Data =
  deposit_root_f :: Hash256
  deposit_count_f :: u64
  block_hash_f :: Hash256

record Validator =
  pubkey_f :: PublicKey
  withdrawal_credentials_f :: Hash256
  effective_balance_f :: u64
  slashed_f :: bool
  activation_eligibility_epoch_f :: Epoch
  activation_epoch_f :: Epoch
  exit_epoch_f :: Epoch
  withdrawable_epoch_f :: Epoch

datatype ParticipationFlags = ParticipationFlags "bool list"

record Checkpoint =
  epoch_f :: Epoch
  root_f :: Hash256

record SyncCommittee =
  pubkeys_f :: "PublicKey Vector"
  aggregate_pubkey_f :: PublicKey

record BeaconState =
  genesis_time_f :: "u64 option"
  genesis_validators_root_f :: "Hash256 option"
  slot_f :: "Slot option"
  fork_f :: "Fork option"
  latest_block_header_f :: "BeaconBlockHeader option"
  block_roots_f :: "Hash256 Vector option"
  state_roots_f :: "Hash256 Vector option"
  historical_roots_f :: "Hash256 List option"
  eth1_data_f :: "Eth1Data option"
  eth1_data_votes_f :: "Eth1Data List option"
  eth1_deposit_index_f :: "u64 option"
  validators_f :: "Validator List option"
  balances_f :: "u64 List option"
  randao_mixes_f :: "Hash256 Vector option"
  slashings_f :: "u64 Vector option"
  previous_epoch_participation_f :: "ParticipationFlags List option"
  current_epoch_participation_f :: "ParticipationFlags List option"
  justification_bits_f :: "Bitvector option"
  previous_justified_checkpoint_f :: "Checkpoint option"
  current_justified_checkpoint_f :: "Checkpoint option"
  finalized_checkpoint_f :: "Checkpoint option"
  inactivity_scores_f :: "u64 List option"
  current_sync_committee_f :: "SyncCommittee option"
  next_sync_committee_f :: "SyncCommittee option"

end