theory Translation_Test
  imports Cont_Monad_Algebra VerifiedConsensus ProcessEpoch "Word_Lib.Word_64" "Word_Lib.More_Arithmetic"
begin

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

context verified_con
begin

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
     (if previous_epoch_target_x3 \<ge> total_active_balance_x2 then do {
           bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 1 False;
           block_root <- get_block_root previous_epoch;
           _  <- (current_justified_checkpoint ::= current_justified_checkpoint\<lparr>epoch_f := previous_epoch, root_f := block_root\<rparr>);
          (justification_bits ::= updated_justification_bits)} else return ());
     (if current_epoch_target_x3 \<ge> total_active_balance_x2 then do {
           bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 0 False;
           block_root <- get_block_root previous_epoch;
           _ <- (current_justified_checkpoint ::= current_justified_checkpoint\<lparr>epoch_f := current_epoch, root_f := block_root\<rparr>);
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

term list_inner

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