theory Translation_Test
  imports Cont_Monad_Algebra ProcessEpoch   "Word_Lib.Word_64" "Word_Lib.More_Arithmetic"
begin



type_synonym ('var, 'val) heap = "'var \<Rightarrow> 'val option"

datatype ('a, 'b) lens = Lens (get : "'a \<Rightarrow> 'b") (set: "'a \<Rightarrow> 'b \<Rightarrow> 'a")

datatype heap_value = list "heap_value list" | u8 word8 | u64 "64 word" 

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
  write_to :: "'a \<Rightarrow> 'b \<Rightarrow> (unit, 'c) cont" ("_ ::= _" [1000, 13] 13)


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

(*

abbreviation (expr_notation)
  write_expr :: "'a \<Rightarrow> 'b \<Rightarrow> (unit, 'c) cont"
  where "write_expr \<equiv> write_to"

nonterminal expr 

term All


syntax
  "_assign_expr" :: "'a \<Rightarrow> expr \<Rightarrow> (unit, 'c) cont " ("_ := _" [1000, 13] 13)
  "_eval_expr"   :: "('d \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> expr \<Rightarrow> expr" ("_ _ _" [1000, 13] 13)
  "_eval_inner"  :: "('d \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> expr" (" _ _ " [1000, 13] 13)
  "_eval_bin_both"    :: "('d \<Rightarrow> 'e \<Rightarrow> 'b) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" (" _ _ _ " [1000, 13] 13)
  "_eval_ref"  :: "'a \<Rightarrow> expr" (" _ ")
  "_eval_val"  :: "'b \<Rightarrow> expr" (" _ ")





abbreviation (input) "with f e \<equiv> bindCont f (\<lambda>b. return (e, b))"  


abbreviation  (input) cont_comp :: "('a \<Rightarrow> ('b, 'r) cont) =>  ('b \<Rightarrow> ('c, 'r) cont) => ('a \<Rightarrow> ('c, 'r) cont)" where 
 "cont_comp f g \<equiv> \<lambda>a. bindCont (f a) g"

abbreviation  (input) "uncurry f \<equiv> (\<lambda>(x,y). f x y)"


abbreviation  (input) compose :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" 
  where "compose f g \<equiv> (\<lambda>x. f (g x))"

term bindCont

 (*  "_expr_final" :: "'b \<Rightarrow> expr" ("_") *)

find_consts "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)"
translations
(* "_assign_expr a (_expr_final b)" \<rightharpoonup> "CONST write_expr a b" *)
 "_assign_expr a (_eval_inner f b)" \<rightharpoonup> "_eval_expr f b (_assign_expr a)"
 "_assign_expr a (_eval_bin_both f b c)" \<rightharpoonup> "CONST bindCont (_eval_expr b) (CONST cont_comp (CONST with (_eval_expr c)) (CONST compose (CONST write_to a) (CONST uncurry f)))"

 "(_eval_expr (_eval_ref a))" \<rightharpoonup> "CONST read a"
 "(_eval_expr (_eval_val a))" \<rightharpoonup> "CONST return a"


 "(_eval_expr (_assign_expr a))" \<rightharpoonup> "CONST write_to a"
 "_eval_expr f b e" \<rightharpoonup> "CONST bindCont (CONST read b)  (CONST compose (_eval_expr e) f) " 


definition "foo (x :: u64 Vector) (y :: nat) = (undefined :: nat)"


term "slashings := plus slashings slashings"

term "slashings := plus randao_mixes (foo slashings 1)"
*)


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
                         _ <- setState ((fst state), (snd state)(p := Some (u8 x))); return ()}"


definition write_u64 :: "'var \<Rightarrow> 64 word \<Rightarrow> (unit, 'a) cont" where
  "write_u64 p x \<equiv> do {state <- getState;
                         _ <- lift_option (do {v <- (snd state p); if (is_u64 v) then Some True else None});
                         setState ((fst state), (snd state)(p := Some (u64 x)))}"

adhoc_overloading
  read read_beacon read_list read_u64 read_u8


adhoc_overloading
  write_to write_beacon write_list write_u8 write_u64

term "(read (x :: 'var)) :: (64 word, 'a) cont"

(* word-based arithmetic *)
definition add :: "64 word \<Rightarrow> 64 word \<Rightarrow> (64 word, 'a) cont" where
  "add x y \<equiv> do {
     let result = x + y;
     if x < result then return result else fail
   }"

lemma add_sanity: "x < 2^64 - 2 \<Longrightarrow> run (add x 1) \<noteq> \<top>"
  apply (clarsimp simp: add_def run_def Let_unfold return_def plus_1_less fail_def)
  by (metis less_x_plus_1 word_order.extremum_strict)

definition mul :: "64 word \<Rightarrow> 64 word \<Rightarrow> (64 word, 'a) cont" where
  "mul x y \<equiv>
     let result = x * y in
     if result div x = y then return result else fail"

lemma mul_sanity: "x = 2 ^ 63 - 1 \<Longrightarrow> y = 2 \<Longrightarrow> run (mul x y) \<noteq> \<top>"
  by (clarsimp simp: mul_def run_def Let_unfold return_def)

lemma mul_sanity_overflow: "x = 2 ^ 63 \<Longrightarrow> y = 2 \<Longrightarrow> run (mul x y) = \<top>"
  by (clarsimp simp: mul_def run_def Let_unfold return_def fail_def)

definition udiv :: "64 word \<Rightarrow> 64 word \<Rightarrow> (64 word, 'a) cont" where
  "udiv x y \<equiv>
     if y \<noteq> 0 then return (x div y) else fail"

lemma udiv_sanity: "run (udiv x 2) \<noteq> \<top>"
  by (clarsimp simp: udiv_def run_def Let_unfold return_def)

lemma udiv_sanity_overflow: "run (udiv x 0) = \<top>"
  by (clarsimp simp: udiv_def run_def Let_unfold fail_def)

definition sub :: "64 word \<Rightarrow> 64 word \<Rightarrow> (64 word, 'a) cont" where
  "sub x y \<equiv>
     let result = x - y in
     if result \<le> x then return result else fail"

lemma sub_sanity: "x > 1 \<Longrightarrow> run (sub x 1) \<noteq> \<top>"
  apply (clarsimp simp: sub_def run_def Let_unfold return_def fail_def)
  by (metis word_not_simps(1) word_sub_1_le)

lemma u64_max: "2^64 - 1 = (-1 :: 64 word)"
  by (metis eq_2_64_0 minus_one_word word_exp_length_eq_0)

lemma sub_sanity_max: "run (sub (2^64 - 1) x) \<noteq> \<top>"
  apply (subst u64_max)
  by (fastforce simp: sub_def run_def Let_unfold return_def fail_def)

lemma sub_sanity_overflow: "y \<noteq> 0 \<Longrightarrow> run (sub 0 y) = \<top>"
  by (fastforce simp: sub_def run_def Let_unfold return_def fail_def)

(* TODO *)
definition get_eligible_validator_indices' :: "(u64 list, 'a) cont" where
  "get_eligible_validator_indices' \<equiv> do {
    previous_epoch \<leftarrow> pick_state (get_previous_epoch config);
    undefined
  }"

abbreviation set_justified_checkpoint :: "Checkpoint \<Rightarrow> (unit, 'a) cont"
  where "set_justified_checkpoint n \<equiv> current_justified_checkpoint ::= n"


definition get_current_epoch :: "(Epoch, 'a) cont" where
  "get_current_epoch \<equiv> do {
     s <- read beacon_slots;
     current_epoch <- lift_option ( (slot_to_u64 s) \\ SLOTS_PER_EPOCH config);
     return (Epoch current_epoch)}"

definition get_previous_epoch :: "(Epoch, 'a) cont" where
  "get_previous_epoch \<equiv> 
   do {current_epoch <- get_current_epoch;
       if current_epoch = GENESIS_EPOCH then return GENESIS_EPOCH else 
                          lift_option ( current_epoch .- Epoch (Unsigned.u64 1))}"

definition get_block_root_at_slot :: "Slot \<Rightarrow> (Hash256, 'a) cont" where
  "get_block_root_at_slot slot \<equiv> do {
    upper_limit \<leftarrow> lift_option (slot .+ Slot (SLOTS_PER_HISTORICAL_ROOT config));
    state_slot <- read beacon_slots;
    _ <- assertion (\<lambda>_. slot < state_slot \<and> state_slot \<le> upper_limit);
    i \<leftarrow> lift_option (slot_to_u64 slot .% SLOTS_PER_HISTORICAL_ROOT config);
    b \<leftarrow> read block_roots;
    lift_option (vector_index b i)
  }"

definition get_block_root :: " Epoch \<Rightarrow> (Hash256, 'a) cont" where
  "get_block_root epoch \<equiv>
    get_block_root_at_slot (compute_start_slot_at_epoch config epoch)"


definition weigh_justification_and_finalization ::
  "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
where
  "weigh_justification_and_finalization total_active_balance
                                        previous_epoch_target_balance
                                        current_epoch_target_balance \<equiv> do {
     previous_epoch <- get_previous_epoch;
     current_epoch <- get_current_epoch;
     old_previous_justified_checkpoint <- read previous_justified_checkpoint;
     old_current_justified_checkpoint  <- read current_justified_checkpoint;
     _ <- (current_justified_checkpoint ::= old_current_justified_checkpoint);
     bits <- read justification_bits;
     let shifted_justification_bits = shift_and_clear_bitvector config bits;
     _ <- (justification_bits ::= shifted_justification_bits);
     previous_epoch_target_x3 \<leftarrow>  lift_option  (previous_epoch_target_balance .* (Unsigned.u64 3));
     current_epoch_target_x3  \<leftarrow>  lift_option  (current_epoch_target_balance .* (Unsigned.u64 3));
     total_active_balance_x2  \<leftarrow>  lift_option  (total_active_balance .* (Unsigned.u64 2));
     (if previous_epoch_target_x3 \<ge> total_active_balance_x2 then do {
           bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 1 False;
           block_root <- get_block_root previous_epoch;
           cjc <- read current_justified_checkpoint; 
           _  <- (current_justified_checkpoint ::= cjc\<lparr>epoch_f := previous_epoch, root_f := block_root\<rparr>);
           _  <- (justification_bits ::= updated_justification_bits);
          return ()} else return ());
     (if current_epoch_target_x3 \<ge> total_active_balance_x2 then do {
           bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 0 False;
           block_root <- get_block_root previous_epoch;
           cjc <- read current_justified_checkpoint; 
           _ <- (current_justified_checkpoint ::= cjc\<lparr>epoch_f := current_epoch, root_f := block_root\<rparr>);
          (justification_bits ::= updated_justification_bits)} else return ());
     bits <- read justification_bits;
     x <- lift_option (epoch_f old_previous_justified_checkpoint .+ Epoch (Unsigned.u64 3));
     _ <- (if (bitvector_all bits 1 4 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ()); 
     x <- lift_option (epoch_f old_previous_justified_checkpoint .+ Epoch (Unsigned.u64 2));
     _ <- (if (bitvector_all bits 1 3 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ());
     _ <- (if (bitvector_all bits 0 3 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ());
     (if (bitvector_all bits 0 2 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ())  
     }"



end