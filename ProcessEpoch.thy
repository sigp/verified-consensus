theory ProcessEpoch                                
  imports Types Invariants Helpers Main "HOL-Library.Monad_Syntax"
begin

context verified_con
begin

definition set_justified_checkpoint :: "Checkpoint \<Rightarrow> (unit, 'a) cont"
  where "set_justified_checkpoint n \<equiv> (current_justified_checkpoint ::= n)"

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
     _ <- (previous_justified_checkpoint ::= old_current_justified_checkpoint);
     bits <- read justification_bits;
     let shifted_justification_bits = shift_and_clear_bitvector config bits;
     _ <- (justification_bits ::= shifted_justification_bits);
     previous_epoch_target_x3 \<leftarrow> previous_epoch_target_balance .* 3;
     current_epoch_target_x3  \<leftarrow> current_epoch_target_balance .* 3;
     total_active_balance_x2  \<leftarrow> total_active_balance .* 2;
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
     x <- epoch_f old_previous_justified_checkpoint .+ Epoch 3;
     _ <- (if (bitvector_all bits 1 4 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ()); 
     x <- epoch_f old_previous_justified_checkpoint .+ Epoch 2;
     _ <- (if (bitvector_all bits 1 3 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ());
     _ <- (if (bitvector_all bits 0 3 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ());
     (if (bitvector_all bits 0 2 \<and> x = current_epoch) then 
        (finalized_checkpoint ::= old_previous_justified_checkpoint) else return ())  
     }"

definition process_justification_and_finalization ::
  "(unit, 'a) cont"
where
  "process_justification_and_finalization \<equiv> do {
     previous_epoch <- get_previous_epoch;
     current_epoch <- get_current_epoch;
     epoch1 \<leftarrow> GENESIS_EPOCH .+ Epoch 1;
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

(* TODO: rewrite with map *)
definition get_flag_index_deltas ::
  "nat \<Rightarrow> ((u64 list \<times> u64 list), 'a) cont"
where
  "get_flag_index_deltas flag_index \<equiv> do {
    v <- read validators;
    let init_rewards = [0. _ \<leftarrow> [0..<length (var_list_inner v)]];
    let init_penalties = init_rewards;
    previous_epoch <- get_previous_epoch;
    unslashed_participating_indices \<leftarrow> get_unslashed_participating_indices flag_index previous_epoch;
    let weight = PARTICIPATION_FLAG_WEIGHTS ! flag_index;
    unslashed_participating_balance \<leftarrow> get_total_balance unslashed_participating_indices;
    unslashed_participating_increment \<leftarrow> unslashed_participating_balance \\
                                            EFFECTIVE_BALANCE_INCREMENT config;
    total_active_balance \<leftarrow> get_total_active_balance ;
    active_increments \<leftarrow> total_active_balance \\ EFFECTIVE_BALANCE_INCREMENT config;
    eligible_validator_indices \<leftarrow> get_eligible_validator_indices;
    foldrM (\<lambda>index opt. do {
      let (rewards, penalties) = opt;
      base_reward \<leftarrow> get_base_reward index;
      in_inactivity_leak \<leftarrow> is_in_inactivity_leak;
      let index_nat = u64_to_nat index;
      if index \<in> unslashed_participating_indices then (
        if \<not> in_inactivity_leak then do {
          reward_numerator_pre \<leftarrow> base_reward .* weight;
          reward_numerator \<leftarrow> reward_numerator_pre .* unslashed_participating_increment;
          reward_denominator \<leftarrow> active_increments .* WEIGHT_DENOMINATOR;
          reward \<leftarrow> reward_numerator \\ reward_denominator;
          total_reward \<leftarrow> rewards ! index_nat .+ reward;
          let rewards' = list_update rewards index_nat total_reward;
          return (rewards', penalties)
        } else (return (rewards, penalties))

      ) else if flag_index \<noteq> TIMELY_HEAD_FLAG_INDEX then do {
        penalty_pre \<leftarrow> base_reward .* weight;
        penalty \<leftarrow> penalty_pre \\ WEIGHT_DENOMINATOR;
        total_penalty \<leftarrow> penalties ! index_nat .+ penalty;
        let penalties' = list_update penalties index_nat total_penalty;
        return (rewards, penalties')
      } else (return (rewards, penalties))
    })  eligible_validator_indices (init_rewards, init_penalties)
  }"

definition get_inactivity_penalty_deltas ::
  "(u64 list \<times> u64 list, 'a) cont"
where
  "get_inactivity_penalty_deltas \<equiv> do {
    v <- read validators;
    let init_rewards = [0. _ \<leftarrow> [0..<length (var_list_inner v)]];
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
      if index \<notin> matching_target_indices then do {
        validator \<leftarrow>  (var_list_index vs index);
        inactivity_score \<leftarrow>  (var_list_index scores index);
        penalty_numerator \<leftarrow> effective_balance_f validator .* inactivity_score;
        penalty_denominator \<leftarrow> INACTIVITY_SCORE_BIAS config .* INACTIVITY_PENALTY_QUOTIENT_ALTAIR;
        penalty \<leftarrow> penalty_numerator \\ penalty_denominator;
        total_penalty \<leftarrow> (penalties ! index_nat) .+ penalty;
        let penalties' = list_update penalties index_nat total_penalty;
        return (rewards, penalties')}
      else
        return (rewards, penalties)}) eligible_validator_indices (init_rewards, init_penalties);
    return (final_rewards, final_penalties)
  }"

(* TODO: use this more? 
definition var_list_update ::
  "'b VariableList \<Rightarrow> u64 \<Rightarrow> 'b \<Rightarrow> ('b VariableList, 'a) cont"
  where
  "var_list_update xs i x \<equiv> do {
    if u64_to_nat i < length (var_list_inner xs) then
      return (VariableList (List.list_update (var_list_inner xs) (u64_to_nat i) x))
    else
      fail
  }"
*)

definition increase_balance ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where
  "increase_balance index reward \<equiv> do {
     orig_balances \<leftarrow> read balances;
     orig_balance \<leftarrow>  (var_list_index orig_balances index);
     new_balance \<leftarrow> orig_balance .+ reward;
     new_balances \<leftarrow> var_list_update new_balance orig_balances index ;
     balances ::= new_balances
  }"

definition decrease_balance ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where
  "decrease_balance index penalty \<equiv> do {
     orig_balances \<leftarrow> read balances;
     orig_balance \<leftarrow>  (var_list_index orig_balances index);
     let new_balance = nat_to_u64 (u64_to_nat orig_balance - u64_to_nat penalty);
     new_balances \<leftarrow> var_list_update new_balance orig_balances index ;
     balances ::= new_balances
  }"

definition apply_rewards_and_penalties 
  where "apply_rewards_and_penalties rp v = do {
      let (rewards, penalties) = rp;
      _ \<leftarrow> mapM (\<lambda>index. do {
        let reward = rewards ! u64_to_nat index;
        let penalty = penalties ! u64_to_nat index;
        _ \<leftarrow> increase_balance index reward;
        decrease_balance index penalty
      }) (map nat_to_u64 [0..<length (var_list_inner v)]);
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
    _ \<leftarrow> mapM (\<lambda>rp. apply_rewards_and_penalties rp v) (flag_deltas @ [inactivity_penalty_deltas]);
    return ()
    }}"

definition get_inactivity_score ::
  "u64 \<Rightarrow> (u64, 'a) cont"
where
  "get_inactivity_score index \<equiv> do {
     scores \<leftarrow> read inactivity_scores;
      (var_list_index scores index)
  }"

definition set_inactivity_score ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
where
  "set_inactivity_score index score \<equiv> do {
     orig_scores \<leftarrow> read inactivity_scores;
     orig_score \<leftarrow>  (var_list_index orig_scores index);
     new_scores \<leftarrow> var_list_update score orig_scores index ;
     inactivity_scores ::= new_scores
  }"

definition process_inactivity_updates ::
  "(unit, 'a) cont"
where
  "process_inactivity_updates \<equiv> do {
    current_epoch \<leftarrow> get_current_epoch;
    if current_epoch = GENESIS_EPOCH then return ()
    else do {
    previous_epoch \<leftarrow> get_previous_epoch;
    eligible_validator_indices \<leftarrow> get_eligible_validator_indices;
    _ \<leftarrow> mapM (\<lambda>index. do {
      unslashed_participating_indices \<leftarrow> get_unslashed_participating_indices
                                          TIMELY_TARGET_FLAG_INDEX
                                          previous_epoch;
      _ \<leftarrow> (if index \<in> unslashed_participating_indices then do {
        current_inactivity_score \<leftarrow> get_inactivity_score index;
        new_inactivity_score \<leftarrow> current_inactivity_score .- (min 1 current_inactivity_score);
        set_inactivity_score index new_inactivity_score
      } else do {
        current_inactivity_score \<leftarrow> get_inactivity_score index;
        new_inactivity_score \<leftarrow> current_inactivity_score .+ INACTIVITY_SCORE_BIAS config;
        set_inactivity_score index new_inactivity_score
      });
      inactivity_leak \<leftarrow> is_in_inactivity_leak;
      _ \<leftarrow> (if \<not> inactivity_leak then do {
        current_inactivity_score \<leftarrow> get_inactivity_score index;
        let decrement = min (INACTIVITY_SCORE_RECOVERY_RATE config) current_inactivity_score;
        new_inactivity_score \<leftarrow> current_inactivity_score .- decrement;
        set_inactivity_score index new_inactivity_score
      } else
        return ()
      );
      return ()
    }) eligible_validator_indices;
    return ()
  }}"


definition sum_vector :: 
  "(64 word) Vector \<Rightarrow> (64 word, 'a) cont" where
"sum_vector vs = foldrM word_unsigned_add (vector_inner vs) 0" 

abbreviation (input) "forM xs f \<equiv> mapM f xs"

definition process_slashings ::
  "(unit, 'a) cont" where
"process_slashings \<equiv> do {
  current_epoch <- get_current_epoch;
  total_balance <- get_total_active_balance;
  sls <- read slashings;
  total_slashings <- sum_vector sls;
  adjusted_slashings <- total_slashings .* PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX;
  let adjusted_total_slashing_balance = min adjusted_slashings total_balance;
  validators <- read validators;
  _ <- forM (enumerate (var_list_inner validators))
     (\<lambda>(index,validator). do {
        vec <- word_unsigned_div (EPOCHS_PER_SLASHINGS_VECTOR config) 2;
        epoch <- epoch_unsigned_add current_epoch (Epoch vec);
        when (slashed_f validator \<and> epoch = withdrawable_epoch_f validator)
            (do { let increment = EFFECTIVE_BALANCE_INCREMENT config;
                   x <- increment .* adjusted_total_slashing_balance;
                   pen_num <- word_unsigned_div (effective_balance_f validator) x;
                   y <- total_balance .* increment;
                   penalty <- word_unsigned_div pen_num y;
                   decrease_balance index penalty})});
  return ()
}"


definition process_effective_balance_updates :: 
  "(unit, 'a) cont" where
 "process_effective_balance_updates \<equiv> do {
       vs <- read validators;
       new_validators <- forM (enumerate (var_list_inner vs))
            (\<lambda>(index, v). do {
               balances <- read balances;
               balance <- var_list_index balances index;
               hysteresis_increment <- word_unsigned_div (EFFECTIVE_BALANCE_INCREMENT config) HYSTERESIS_QUOTIENT;
               downward_threshold <- hysteresis_increment .* HYSTERESIS_DOWNWARD_MULTIPLIER;
               upward_threshold <- hysteresis_increment .* HYSTERESIS_UPWARD_MULTIPLIER;
               lower <- balance .+ downward_threshold;
               let effective_balance = effective_balance_f v;
               upper <- effective_balance .+ upward_threshold;
               if (lower < effective_balance \<or> upper < balance)
                   then (do { b <- word_unsigned_mod balance (EFFECTIVE_BALANCE_INCREMENT config);
                          b' <- balance .- b;
                          return (v\<lparr>effective_balance_f := min b' (MAX_EFFECTIVE_BALANCE)\<rparr>)})
                   else  (return v)});
         (write_to validators (VariableList new_validators))}
 "

definition process_eth1_data_reset :: 
 "(unit, 'a) cont" where
 "process_eth1_data_reset \<equiv> do {
  epoch <- get_current_epoch;
  next_epoch <- epoch_to_u64 epoch .+ ( 1);
  x <- ( next_epoch) .% (EPOCHS_PER_ETH1_VOTING_PERIOD config);
  when (x = 0) ( eth1_data_votes ::= (VariableList [])) 
  }"

term var_list_update

definition process_slashings_reset ::
 "(unit, 'a) cont" where
 "process_slashings_reset = do {
    epoch <- get_current_epoch;
    next_epoch <- epoch_to_u64 epoch .+ ( 1);
    x <- next_epoch .% EPOCHS_PER_SLASHINGS_VECTOR config;
    (slashings := vector_update 0 slashings x)
  }"



definition get_randao_mix ::
 "Epoch \<Rightarrow> (Hash256, 'a) cont"
 where "get_randao_mix epoch \<equiv> do {
  mixes <- read randao_mixes;
  index <- (epoch_to_u64 epoch) .% EPOCHS_PER_HISTORICAL_VECTOR config;
  vector_index mixes index
 }"

definition process_randao_mixes_reset ::
"(unit, 'a) cont" where
 "process_randao_mixes_reset = do {
    epoch <- get_current_epoch;
    next_epoch <- epoch_to_u64 epoch .+ ( 1);
    x <- next_epoch .% EPOCHS_PER_HISTORICAL_VECTOR config;
    randao_mix <- get_randao_mix epoch;
   (randao_mixes := vector_update randao_mix randao_mixes x)
}"
end

end