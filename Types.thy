theory Types
  imports Main Unsigned
begin

datatype Hash256 = Hash256 "u8 list"

(* FIXME: enforce length at type level? *)
datatype 'a Vector = Vector "'a list"
datatype 'a List = List "'a list"

datatype Bitvector = Bitvector "bool list"

datatype PublicKey = PublicKey "u8 list"

datatype Version = Version "u8 list"

record Fork =
  previous_version :: Version
  current_version :: Version
  epoch :: Epoch

record BeaconBlockHeader =
  slot :: Slot
  proposer_index :: u64
  parent_root :: Hash256
  state_root :: Hash256
  body_root :: Hash256

record Eth1Data =
  deposit_root :: Hash256
  deposit_count :: u64
  block_hash :: Hash256

record Validator =
  pubkey :: PublicKey
  withdrawal_credentials :: Hash256
  effective_balance :: u64
  slashed :: bool
  activation_eligibility_epoch :: Epoch
  activation_epoch :: Epoch
  exit_epoch :: Epoch
  withdrawable_epoch :: Epoch

datatype ParticipationFlags = ParticipationFlags "bool list"

record Checkpoint =
  epoch :: Epoch
  root :: Hash256

record SyncCommittee =
  pubkeys :: "PublicKey Vector"
  aggregate_pubkey :: PublicKey

record BeaconState =
  genesis_time :: u64
  genesis_validators_root :: Hash256
  slot :: Slot
  fork :: Fork
  latest_block_header :: BeaconBlockHeader
  block_roots :: "Hash256 Vector"
  state_roots :: "Hash256 Vector"
  historical_roots :: "Hash256 List"
  eth1_data :: Eth1Data
  eth1_data_votes :: "Eth1Data List"
  eth1_deposit_index :: u64
  validators :: "Validator List"
  balances :: "u64 List"
  randao_mixes :: "Hash256 Vector"
  slashings :: "u64 Vector"
  previous_epoch_participation :: "ParticipationFlags List"
  current_epoch_participation :: "ParticipationFlags List"
  justification_bits :: Bitvector
  previous_justified_checkpoint :: Checkpoint
  current_justified_checkpoint :: Checkpoint
  finalized_checkpoint :: Checkpoint
  inactivity_scores :: "u64 List"
  current_sync_committee :: SyncCommittee
  next_sync_committee :: SyncCommittee

end