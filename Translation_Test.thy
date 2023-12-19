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
                        setState ((fst state), (snd state)(p := Some (u8 x)))}"


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

abbreviation 
  "when b p \<equiv> (if b then p else return ())" 

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


definition set_justified_checkpoint :: "Checkpoint \<Rightarrow> (unit, 'a) cont"
  where "set_justified_checkpoint n \<equiv> (current_justified_checkpoint ::= n)"


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
     current_epoch  <- get_current_epoch;
     old_previous_justified_checkpoint <- read previous_justified_checkpoint;
     old_current_justified_checkpoint  <- read current_justified_checkpoint;
     _ <- (current_justified_checkpoint ::= old_current_justified_checkpoint);
     bits <- read justification_bits;
     let shifted_justification_bits = shift_and_clear_bitvector config bits;
     _ <- (justification_bits ::= shifted_justification_bits);
     previous_epoch_target_x3 \<leftarrow>  lift_option  (previous_epoch_target_balance .* (Unsigned.u64 3));
     current_epoch_target_x3  \<leftarrow>  lift_option  (current_epoch_target_balance .* (Unsigned.u64 3));
     total_active_balance_x2  \<leftarrow>  lift_option  (total_active_balance .* (Unsigned.u64 2));
     when (previous_epoch_target_x3 \<ge> total_active_balance_x2)
      (do {bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 1 False;
           block_root <- get_block_root previous_epoch;
           _  <- (current_justified_checkpoint ::= current_justified_checkpoint\<lparr>epoch_f := previous_epoch, root_f := block_root\<rparr>);
          (justification_bits ::= updated_justification_bits)});
     when (current_epoch_target_x3 \<ge> total_active_balance_x2) 
      (do {bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 0 False;
           block_root <- get_block_root previous_epoch;
           _ <- (current_justified_checkpoint ::= current_justified_checkpoint\<lparr>epoch_f := current_epoch, root_f := block_root\<rparr>);
          (justification_bits ::= updated_justification_bits)});
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


definition get_active_validator_indices :: "Epoch \<Rightarrow> (u64 list, 'a) cont" where
  "get_active_validator_indices  e \<equiv> do {
    v <- read validators; 
    return ([i. (i, v) \<leftarrow> enumerate (list_inner v), is_active_validator v e])}"

definition get_eligible_validator_indices :: "(u64 list, 'a) cont" where
  "get_eligible_validator_indices \<equiv> do {
    previous_epoch <- get_previous_epoch ;
    previous_epoch_p1 \<leftarrow> lift_option (previous_epoch .+ Epoch (Unsigned.u64 1));
    v <- read validators; 
    return [i. (i, v) \<leftarrow> enumerate (list_inner v),
            is_active_validator v previous_epoch \<or>
            (slashed_f v \<and> previous_epoch_p1 < withdrawable_epoch_f v)]
  }"


definition get_unslashed_participating_indices ::
   " nat \<Rightarrow> Epoch \<Rightarrow> (u64 set, 'a) cont"
where
  "get_unslashed_participating_indices flag_index e \<equiv> do {
    previous_epoch <- get_previous_epoch ;
    current_epoch <- get_current_epoch ;
    _ \<leftarrow> assertion (\<lambda>_. e = previous_epoch \<or> e = current_epoch);
    epoch_participation <- (if e = current_epoch then read current_epoch_participation
                                                 else read previous_epoch_participation);
    active_validator_indices <- get_active_validator_indices e;
    let participating_indices = [
      i.
      i \<leftarrow> active_validator_indices,
      has_flag (unsafe_list_index epoch_participation i) flag_index
    ];
    v <- read validators;
    return (
      list.set (
        filter (\<lambda>index. \<not> slashed_f (unsafe_list_index v index))
               participating_indices))
  }"


definition get_total_balance :: " u64 set \<Rightarrow> (u64, 'a) cont" where
  "get_total_balance indices \<equiv> do {
    v <- read validators;
    total \<leftarrow> lift_option (safe_sum ((\<lambda>i. effective_balance_f (unsafe_list_index (v) i)) ` indices));
    return (max (EFFECTIVE_BALANCE_INCREMENT config) total)
  }"


definition get_total_active_balance :: " (u64, 'a) cont" where
  "get_total_active_balance  \<equiv> do {
   current_epoch <- get_current_epoch;
   inds <- get_active_validator_indices current_epoch;
   get_total_balance (list.set inds)} "

definition process_justification_and_finalization ::
  " (unit, 'a) cont"
where
  "process_justification_and_finalization \<equiv> do {
     previous_epoch <- get_previous_epoch;
     current_epoch <- get_current_epoch;
     epoch1 \<leftarrow> lift_option (GENESIS_EPOCH .+ Epoch (Unsigned.u64 1));
    if current_epoch \<le> epoch1 then
      return ()
    else do {
      previous_indices \<leftarrow> 
        get_unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX previous_epoch;
      current_indices \<leftarrow>
        get_unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX current_epoch;
      total_active_balance    \<leftarrow> get_total_active_balance;
      previous_target_balance \<leftarrow> get_total_balance  previous_indices;
      current_target_balance  \<leftarrow> get_total_balance  previous_indices;
      weigh_justification_and_finalization
         total_active_balance previous_target_balance current_target_balance
    }
  }"

term mapM


definition get_base_reward_per_increment :: " (u64, 'a) cont" where
  "get_base_reward_per_increment \<equiv> do {
    total_active_balance \<leftarrow> get_total_active_balance;
    sqrt_total_active_balance \<leftarrow> lift_option (integer_squareroot total_active_balance);
    x <- lift_option (EFFECTIVE_BALANCE_INCREMENT config .* BASE_REWARD_FACTOR config);
    lift_option (sqrt_total_active_balance \\ x)
  }"

definition get_base_reward :: " u64 \<Rightarrow> (u64, 'a) cont" where
  "get_base_reward index \<equiv> do {
    v <- read validators;
    validator \<leftarrow> lift_option (list_index v index);
    increments \<leftarrow> lift_option (effective_balance_f validator \\ EFFECTIVE_BALANCE_INCREMENT config);
    base_reward_per_increment \<leftarrow> get_base_reward_per_increment;
    lift_option (increments .* base_reward_per_increment)
  }"


definition get_finality_delay :: " (u64, 'a) cont" where
  "get_finality_delay \<equiv> do {
    previous_epoch <- get_previous_epoch;
    final <- read finalized_checkpoint;
    lift_option ( epoch_to_u64 previous_epoch .- epoch_to_u64 (epoch_f final))}"

definition is_in_inactivity_leak :: "(bool, 'a) cont" where
  "is_in_inactivity_leak \<equiv> do {
    finality_delay \<leftarrow> get_finality_delay;
    return (finality_delay > MIN_EPOCHS_TO_INACTIVITY_PENALTY config)
  }"

(* TODO: rewrite with map *)
definition get_flag_index_deltas ::
  "nat \<Rightarrow> ((u64 list \<times> u64 list), 'a) cont"
where
  "get_flag_index_deltas flag_index \<equiv> do {
    v <- read validators;
    let init_rewards = [(Unsigned.u64 0). _ \<leftarrow> [0..<length (list_inner v)]];
    let init_penalties = init_rewards;
    previous_epoch <- get_previous_epoch;
    unslashed_participating_indices \<leftarrow> get_unslashed_participating_indices flag_index previous_epoch;
    let weight = PARTICIPATION_FLAG_WEIGHTS ! flag_index;
    unslashed_participating_balance \<leftarrow> get_total_balance unslashed_participating_indices;
    unslashed_participating_increments \<leftarrow> lift_option (unslashed_participating_balance \\
                                            EFFECTIVE_BALANCE_INCREMENT config);
    total_active_balance \<leftarrow> get_total_active_balance ;
    active_increments \<leftarrow> lift_option (total_active_balance \\ EFFECTIVE_BALANCE_INCREMENT config);
    eligible_validator_indices \<leftarrow> get_eligible_validator_indices;
    foldrM (\<lambda>index opt. do {
      let (rewards, penalties) = opt;
      base_reward \<leftarrow> get_base_reward index;
      in_inactivity_leak \<leftarrow> is_in_inactivity_leak;
      let index_nat = u64_to_nat index;
      if index \<in> unslashed_participating_indices then (
        if \<not> in_inactivity_leak then lift_option (do {
          reward_numerator \<leftarrow> base_reward .* weight \<bind> flip (.*) unslashed_participating_increments;
          reward_denominator \<leftarrow> active_increments .* WEIGHT_DENOMINATOR;
          reward \<leftarrow> reward_numerator \\ reward_denominator;
          total_reward \<leftarrow> rewards ! index_nat .+ reward;
          let rewards' = list_update rewards index_nat total_reward;
          Some (rewards', penalties)
        }) else (return (rewards, penalties))

      ) else if flag_index \<noteq> TIMELY_HEAD_FLAG_INDEX then lift_option (do {
        penalty \<leftarrow> base_reward .* weight \<bind> (flip (\\) WEIGHT_DENOMINATOR);
        total_penalty \<leftarrow> penalties ! index_nat .+ penalty;
        let penalties' = list_update penalties index_nat total_penalty;
        Some (rewards, penalties')
      }) else (return (rewards, penalties))
    })  eligible_validator_indices (init_rewards, init_penalties)
  }"


definition get_inactivity_penalty_deltas ::
  "(u64 list \<times> u64 list, 'a) cont"
where
  "get_inactivity_penalty_deltas \<equiv> do {
    v <- read validators;
    let init_rewards = [(Unsigned.u64 0). _ \<leftarrow> [0..<length (list_inner v)]];
    let init_penalties = init_rewards;
    previous_epoch <- get_previous_epoch;
    matching_target_indices \<leftarrow> get_unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX
                                                                   previous_epoch;
    eligible_validator_indices \<leftarrow> get_eligible_validator_indices;
    vs <- read validators;
    scores <- read inactivity_scores; 
    (final_rewards, final_penalties) <- foldrM (\<lambda>index opt. do {
      let (rewards, penalties) = opt;
      let index_nat = u64_to_nat index;
      if index \<notin> matching_target_indices then lift_option (do {
        validator \<leftarrow> list_index vs index;
        inactivity_score \<leftarrow> list_index scores index;
        penalty_numerator \<leftarrow> effective_balance_f validator .* inactivity_score;
        penalty_denominator \<leftarrow> INACTIVITY_SCORE_BIAS config .* INACTIVITY_PENALTY_QUOTIENT_ALTAIR;
        penalty \<leftarrow> penalty_numerator \\ penalty_denominator;
        total_penalty \<leftarrow> (penalties ! index_nat) .+ penalty;
        let penalties' = list_update penalties index_nat total_penalty;
        Some (rewards, penalties')}) 
      else
        return (rewards, penalties)}) eligible_validator_indices (init_rewards, init_penalties);
    return (final_rewards, final_penalties)
  }"

definition list_update ::
  "'b List \<Rightarrow> u64 \<Rightarrow> 'b \<Rightarrow> ('b List, 'a) cont"
  where
  "list_update xs i x \<equiv> do {
    if u64_to_nat i < length (list_inner xs) then
      return (List (List.list_update (list_inner xs) (u64_to_nat i) x))
    else
      fail
  }"

definition increase_balance ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where
  "increase_balance index reward \<equiv> do {
     orig_balances \<leftarrow> read balances;
     orig_balance \<leftarrow> lift_option (list_index orig_balances index);
     new_balance \<leftarrow> lift_option (orig_balance .+ reward);
     new_balances \<leftarrow> list_update orig_balances index new_balance;
     balances ::= new_balances
  }"

definition decrease_balance ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where
  "decrease_balance index penalty \<equiv> do {
     orig_balances \<leftarrow> read balances;
     orig_balance \<leftarrow> lift_option (list_index orig_balances index);
     let new_balance = Unsigned.u64 (u64_to_nat orig_balance - u64_to_nat penalty);
     new_balances \<leftarrow> list_update orig_balances index new_balance;
     balances ::= new_balances
  }"

definition apply_rewards_and_penalties 
  where "apply_rewards_and_penalties rp v = do {
      let (rewards, penalties) = rp;
      mapM (\<lambda>index. do {
        reward \<leftarrow> lift_option (Some (rewards ! u64_to_nat index));
        penalty \<leftarrow> lift_option (Some (penalties ! u64_to_nat index));
        increase_balance index reward;
        decrease_balance index penalty
      }) (map Unsigned.u64 [0..<length (list_inner v)]);
      return ()
  }"

definition process_rewards_and_penalties ::
  "(unit, 'a) cont"
where
  "process_rewards_and_penalties \<equiv> do {
    v <- read validators;
    current_epoch <- get_current_epoch;
    if current_epoch = GENESIS_EPOCH then return ()
    else do {

    flag_deltas \<leftarrow> foldrM (\<lambda>flag_index all_deltas. do {
      flag_index_deltas \<leftarrow> get_flag_index_deltas flag_index;
      return (all_deltas @ [flag_index_deltas])
    }) [0..<length PARTICIPATION_FLAG_WEIGHTS] [];

    inactivity_penalty_deltas \<leftarrow> get_inactivity_penalty_deltas;
    mapM (\<lambda>rp. apply_rewards_and_penalties rp v) (flag_deltas @ [inactivity_penalty_deltas]);
    return ()
    }}"




end

end