theory Types
  imports Main "Word_Lib.Word_64" "Word_Lib.Word_8"
begin

(*
 * We use names ending in _f for all record fields to prevent the unadorned name becoming
 * unusable. See: https://isabelle.in.tum.de/dist/library/Doc/Tutorial/Records.html
*)

type_synonym u8 = "8 word"
type_synonym u64 = "64 word"
type_synonym u256 = "256 word"
type_synonym ExecutionAddress = "160 word"
datatype Slot = Slot u64
datatype Epoch = Epoch (raw_epoch: u64)



datatype Hash256 = Hash256 "u8 list"
datatype 'a Vector = Vector "'a list"
datatype 'a VariableList = VariableList "'a list"

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

datatype ParticipationFlags = ParticipationFlags (participation_flag_weights: "bool list")

record Checkpoint =
  epoch_f :: Epoch
  root_f :: Hash256

record SyncCommittee =
  pubkeys_f :: "PublicKey Vector"
  aggregate_pubkey_f :: PublicKey

record ExecutionPayloadHeader =
  parent_hash_f :: Hash256
  fee_recipient_f :: ExecutionAddress
  state_root_f :: Hash256
  receipts_root_f :: Hash256
  logs_bloom_f :: "u8 list"
  prev_randao_f :: Hash256
  block_number_f :: u64
  gas_limit_f :: u64
  timestamp_f :: u64
  extra_data_f :: "u8 list"
  base_fee_per_gas_f :: u256
  block_hash_f :: Hash256
  transactions_root_f :: Hash256
  withdrawals_root_f :: Hash256

record HistoricalSummary =
  block_summary_root_f :: Hash256
  state_summary_root_f :: Hash256

record BeaconState =
  genesis_time_f :: "u64 option"
  genesis_validators_root_f :: "Hash256 option"
  slot_f :: "Slot option"
  fork_f :: "Fork option"
  latest_block_header_f :: "BeaconBlockHeader option"
  block_roots_f :: "Hash256 Vector option"
  state_roots_f :: "Hash256 Vector option"
  historical_roots_f :: "Hash256 VariableList option"
  eth1_data_f :: "Eth1Data option"
  eth1_data_votes_f :: "Eth1Data VariableList option"
  eth1_deposit_index_f :: "u64 option"
  validators_f :: "Validator VariableList option"
  balances_f :: "u64 VariableList option"
  randao_mixes_f :: "Hash256 Vector option"
  slashings_f :: "u64 Vector option"
  previous_epoch_participation_f :: "ParticipationFlags VariableList option"
  current_epoch_participation_f :: "ParticipationFlags VariableList option"
  justification_bits_f :: "Bitvector option"
  previous_justified_checkpoint_f :: "Checkpoint option"
  current_justified_checkpoint_f :: "Checkpoint option"
  finalized_checkpoint_f :: "Checkpoint option"
  inactivity_scores_f :: "u64 VariableList option"
  current_sync_committee_f :: "SyncCommittee option"
  next_sync_committee_f :: "SyncCommittee option"
  latest_execution_payload_header :: "ExecutionPayloadHeader option"
  next_withdrawal_index_f :: "u64 option"
  next_withdrawal_validator_index_f :: "u64 option"
  historical_summaries_f :: "HistoricalSummary VariableList option"

end