(* Definition of the `verified_con` locale which is used in the rest of the project *)
theory VerifiedConsensus
  imports Cont_Monad_Algebra Types Config "Word_Lib.Word_64" "Word_Lib.More_Arithmetic"
begin

type_synonym ('var, 'val) heap = "'var \<Rightarrow> 'val option"

datatype ('a, 'b) lens = Lens (get : "'a \<Rightarrow> 'b") (set: "'a \<Rightarrow> 'b \<Rightarrow> 'a")

datatype heap_value = list "heap_value list" | u8 u8 | u64 u64

primrec is_list where
  "is_list (list _) = True"|
  "is_list (u8 _) = False" |
  "is_list (u64 _) = False"

primrec list_of where
  "list_of (list xs) = Some xs"|
  "list_of (u8 _)    = None" |
  "list_of (u64 _)   = None"


primrec is_u8 where
  "is_u8 (list _) = False"|
  "is_u8 (u8 _) = True" |
  "is_u8 (u64 _) = False"


primrec u8_of where
  "u8_of (list _) = None"|
  "u8_of (u8 x)   = Some x" |
  "u8_of (u64 _)  = None"


primrec is_u64 where
  "is_u64 (list _) = False"|
  "is_u64 (u8 _)   = False"|
  "is_u64 (u64 _)  = True"



primrec u64_of where
  "u64_of (list _) = None"|
  "u64_of (u8 _)   = None" |
  "u64_of (u64 x)  = Some x"

consts
  read :: "'a \<Rightarrow> ('b, 'c) cont"

consts 
  write_to :: "'a \<Rightarrow> 'b \<Rightarrow> (unit, 'c) cont" 

abbreviation modify :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> (unit, 'c) cont" where
   "modify a f \<equiv> (bindCont (read a) (\<lambda>x. write_to a (f x)))"

definition "genesis_time = Lens genesis_time_f (\<lambda>a b. a\<lparr>genesis_time_f := b\<rparr> )"

definition "genesis_validators_root = Lens genesis_validators_root_f  (\<lambda>a b. a\<lparr>genesis_validators_root_f := b\<rparr> )"

definition "beacon_slots = Lens BeaconState.slot_f  (\<lambda>a b. a\<lparr> BeaconState.slot_f := b\<rparr> )"

definition "fork         = Lens fork_f  (\<lambda>a b. a\<lparr>fork_f := b\<rparr> )"

definition "latest_block_header = Lens latest_block_header_f  (\<lambda>a b. a\<lparr>latest_block_header_f := b\<rparr> )"

definition "block_roots = Lens block_roots_f  (\<lambda>a b. a\<lparr>block_roots_f := b\<rparr> )"

definition "state_roots = Lens state_roots_f  (\<lambda>a b. a\<lparr>state_roots_f := b\<rparr> )"

definition "historical_roots = Lens historical_roots_f  (\<lambda>a b. a\<lparr>historical_roots_f := b\<rparr> )"

definition "eth1_data = Lens eth1_data_f  (\<lambda>a b. a\<lparr>eth1_data_f := b\<rparr> )"

definition "eth1_data_votes = Lens eth1_data_votes_f  (\<lambda>a b. a\<lparr>eth1_data_votes_f := b\<rparr> )"

definition "eth1_deposit_index = Lens eth1_deposit_index_f  (\<lambda>a b. a\<lparr>eth1_deposit_index_f := b\<rparr> )"

definition "validators = Lens validators_f  (\<lambda>a b. a\<lparr>validators_f := b\<rparr> )"

definition "balances = Lens balances_f  (\<lambda>a b. a\<lparr>balances_f := b\<rparr> )"

definition "randao_mixes = Lens randao_mixes_f  (\<lambda>a b. a\<lparr>randao_mixes_f := b\<rparr> )"

definition "slashings = Lens slashings_f  (\<lambda>a b. a\<lparr>slashings_f := b\<rparr> )"

definition "previous_epoch_participation = Lens previous_epoch_participation_f  (\<lambda>a b. a\<lparr>previous_epoch_participation_f := b\<rparr> )"

definition "current_epoch_participation = Lens current_epoch_participation_f  (\<lambda>a b. a\<lparr>current_epoch_participation_f := b\<rparr> )"

definition "justification_bits = Lens justification_bits_f  (\<lambda>a b. a\<lparr>justification_bits_f := b\<rparr> )"

definition "previous_justified_checkpoint = Lens previous_justified_checkpoint_f  (\<lambda>a b. a\<lparr>previous_justified_checkpoint_f := b\<rparr> )"

definition "current_justified_checkpoint = Lens current_justified_checkpoint_f  (\<lambda>a b. a\<lparr>current_justified_checkpoint_f := b\<rparr> )"

definition "finalized_checkpoint = Lens finalized_checkpoint_f  (\<lambda>a b. a\<lparr>finalized_checkpoint_f := b\<rparr> )"

definition "inactivity_scores = Lens inactivity_scores_f  (\<lambda>a b. a\<lparr>inactivity_scores_f := b\<rparr> )"

definition "current_sync_committee = Lens current_sync_committee_f  (\<lambda>a b. a\<lparr>current_sync_committee_f := b\<rparr> )"

definition "next_sync_committee = Lens next_sync_committee_f  (\<lambda>a b. a\<lparr>next_sync_committee_f := b\<rparr> )"

syntax
  "_mod_expr" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c " ("_ ::= _" [1000, 13] 13)


translations
 "_mod_expr a b" \<rightharpoonup> "CONST modify a (\<lambda>a. b)"

definition foo where 
   "foo x y \<equiv>  (x ::= y)"

thm foo_def

locale verified_con = constrained_atomic +
  constrains pgm  :: "(BeaconState \<times> ('var, heap_value) heap) rel \<Rightarrow> 'a"
  constrains env  :: "(BeaconState \<times> ('var, heap_value) heap) rel \<Rightarrow> 'a"
  constrains test :: "(BeaconState \<times> ('var, heap_value) heap) set \<Rightarrow> 'a"
  fixes config :: "Config"

begin

lemma nil_not_top[simp]: "(nil = \<top>) = False"
  by (metis (full_types) UNIV_I abstract_hom_commands.hom_iso_eq empty_iff seq_abort seq_nil_left
      test.abstract_hom_commands_axioms)

definition read_beacon :: "((BeaconState, 'b option) lens) \<Rightarrow> ('b, 'a) cont" where
  "read_beacon l \<equiv> do { state \<leftarrow> getState; if (get l (fst state)) = None then fail else return (the (get l (fst state))) }"


definition write_beacon :: "((BeaconState, 'b option) lens) \<Rightarrow> 'b \<Rightarrow> (unit, 'a) cont" where
  "write_beacon l b \<equiv> do { state \<leftarrow> getState; 
                          if (get l (fst state)) = None then fail else
                          setState (set l (fst state) (Some b), (snd state))  }"

definition "lift_option v = (if v = None then fail else return (the v))"

definition read_list :: "'var \<Rightarrow> (heap_value list, 'a) cont" where
  "read_list p \<equiv> do {state <- getState; 
                     lift_option (do {v <- (snd state p); list_of v})}"

definition read_u8 :: "'var \<Rightarrow> (8 word, 'a) cont" where
  "read_u8 p \<equiv> do {state <- getState; 
                   lift_option (do {v <- (snd state p); u8_of v})}"


definition read_u64 :: "'var \<Rightarrow> (64 word, 'a) cont" where
  "read_u64 p \<equiv> do {state <- getState; 
                     x <- lift_option (do {v <- (snd state p); u64_of v});
                     return x}"


definition write_list :: "'var \<Rightarrow> heap_value list \<Rightarrow> (unit, 'a) cont" where
  "write_list p x \<equiv> do {state <- getState;
                          _ <- lift_option (do {v <- (snd state p); if (is_list v) then Some True else None});
                         setState ((fst state), fun_upd (snd state) p (Some (list x)))}"


definition write_u8 :: "'var \<Rightarrow> 8 word \<Rightarrow> (unit, 'a) cont" where
  "write_u8 p x \<equiv> do {state <- getState;
                         _ <- lift_option (do {v <- (snd state p); if (is_u8 v) then Some True else None});
                        setState ((fst state), (snd state)(p := Some (u8 x)))}"


definition write_u64 :: "'var \<Rightarrow> 64 word \<Rightarrow> (unit, 'a) cont" where
  "write_u64 p x \<equiv> do {state <- getState;
                         _ <- lift_option (do {v <- (snd state p); if (is_u64 v) then Some True else None});
                         setState ((fst state), (snd state)(p := Some (u64 x)))}"

adhoc_overloading
  read read_beacon read_list read_u64 read_u8


adhoc_overloading
  write_to write_beacon write_list write_u8 write_u64

end

end