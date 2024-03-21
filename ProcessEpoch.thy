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
     _ <- when (previous_epoch_target_x3 \<ge> total_active_balance_x2)
      (do {bits <- read justification_bits;
           let updated_justification_bits = bitvector_update bits 1 False;
           block_root <- get_block_root previous_epoch;
           _  <- (current_justified_checkpoint ::= current_justified_checkpoint\<lparr>epoch_f := previous_epoch, root_f := block_root\<rparr>);
          (justification_bits ::= updated_justification_bits)});
     _ <- when (current_epoch_target_x3 \<ge> total_active_balance_x2)
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

definition update_validator :: "Validator \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where "update_validator val index \<equiv> do {
   vs \<leftarrow> read validators;
   vs \<leftarrow> var_list_update val vs index;
   write_to validators vs
}"

definition process_effective_balance_updates :: 
  "(unit, 'a) cont" where
 "process_effective_balance_updates \<equiv> do {
       vs <- read validators;
       _ <- forM (enumerate (var_list_inner vs))
            (\<lambda>(index, v). do {
               balances <- read balances;
               balance <- var_list_index balances index;
               hysteresis_increment <- word_unsigned_div (EFFECTIVE_BALANCE_INCREMENT config) HYSTERESIS_QUOTIENT;
               downward_threshold <- hysteresis_increment .* HYSTERESIS_DOWNWARD_MULTIPLIER;
               upward_threshold <- hysteresis_increment .* HYSTERESIS_UPWARD_MULTIPLIER;
               lower <- balance .+ downward_threshold;
               let effective_balance = effective_balance_f v;
               upper <- effective_balance .+ upward_threshold;
               v \<leftarrow> if (lower < effective_balance \<or> upper < balance)
                      then (do { b <- word_unsigned_mod balance (EFFECTIVE_BALANCE_INCREMENT config);
                          b' <- balance .- b;
                          return (v\<lparr>effective_balance_f := min b' (MAX_EFFECTIVE_BALANCE)\<rparr>)})
                       else (return v);
               update_validator v index});
         return ()}"

definition process_eth1_data_reset :: 
 "(unit, 'a) cont" where
 "process_eth1_data_reset \<equiv> do {
  epoch <- get_current_epoch;
  next_epoch <- epoch_to_u64 epoch .+ ( 1);
  x <- ( next_epoch) .% (EPOCHS_PER_ETH1_VOTING_PERIOD config);
  when (x = 0) ( eth1_data_votes ::= (VariableList [])) 
  }"

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

primrec maximum where
 "maximum c (x#xs) = (if c \<ge> x then maximum c xs else maximum x xs)" |
 "maximum c [] = c"


definition compute_activation_exit_epoch :: " Epoch \<Rightarrow> (Epoch, 'a) cont"
  where "compute_activation_exit_epoch epoch \<equiv> do {
  x \<leftarrow> epoch .+ (Epoch 1);
  x \<leftarrow> x .+ MAX_SEED_LOOKAHEAD;
  return x  
}"

definition get_validator_churn_limit :: "(u64, 'a) cont"
  where "get_validator_churn_limit = do {
         current_epoch \<leftarrow> get_current_epoch;
         active_validator_indices \<leftarrow> get_active_validator_indices(current_epoch);
         x \<leftarrow> word_unsigned_div ( nat_to_u64 (length (active_validator_indices)))
          (CHURN_LIMIT_QUOTIENT config);
         return (max (MIN_PER_EPOCH_CHURN_LIMIT config) x)
}"

definition initiate_validator_exit :: "u64 \<Rightarrow> (unit, 'a) cont" 
  where "initiate_validator_exit index \<equiv> do {
    vs <- read validators;
    val <- var_list_index vs index;
    _ \<leftarrow> when (exit_epoch_f val = FAR_FUTURE_EPOCH)
      (do {
       let exit_epochs = map exit_epoch_f (filter (\<lambda>v. exit_epoch_f v \<noteq> FAR_FUTURE_EPOCH) (var_list_inner vs));
       current_epoch <- get_current_epoch;
       activation_exit_epoch \<leftarrow> compute_activation_exit_epoch current_epoch;
       let exit_queue_epoch = maximum activation_exit_epoch exit_epochs;
       let exit_queue_churn = length (filter (\<lambda>v. exit_epoch_f v = exit_queue_epoch) (var_list_inner vs));
       churn_limit <- get_validator_churn_limit;
       exit_queue_epoch \<leftarrow> (if (nat_to_u64 exit_queue_churn < churn_limit) then return exit_queue_epoch
                                                                 else exit_queue_epoch .+ Epoch 1);
       let val = val\<lparr>exit_epoch_f :=  exit_queue_epoch\<rparr>;
       new_withdrawable_epoch \<leftarrow> epoch_to_u64 (exit_epoch_f val) .+ MIN_VALIDATOR_WITHDRAWABILITY_DELAY config;
       let val = val\<lparr>withdrawable_epoch_f := Epoch (new_withdrawable_epoch) \<rparr>;
       vs \<leftarrow> var_list_update val vs index;
       write_to validators vs
    });
    return ()
  }"

definition is_active_validator :: "Validator \<Rightarrow> Epoch \<Rightarrow> bool"
  where "is_active_validator validator epoch \<equiv>
           activation_epoch_f validator \<le> epoch \<and> epoch < exit_epoch_f validator"


definition is_eligible_for_activation :: "Validator \<Rightarrow> (bool, 'a) cont"
  where "is_eligible_for_activation validator \<equiv> do {
         final \<leftarrow> read finalized_checkpoint;
         return (activation_eligibility_epoch_f validator \<le> epoch_f final \<and>
                 activation_epoch_f validator = FAR_FUTURE_EPOCH) 
}"

primrec filterM :: "('b \<Rightarrow> (bool, 'r) cont) \<Rightarrow> 'b list \<Rightarrow> ('b list, 'r) cont" where
  "filterM f (x#xs) = bindCont (f x) (\<lambda>b. do { xs <- filterM f xs; (if b then return (x # xs) else return xs)}) " |
  "filterM f [] = return []"

fun sortedByM :: "('b \<Rightarrow> 'b \<Rightarrow> (bool, 'a) cont) \<Rightarrow> 'b list \<Rightarrow> (bool, 'a) cont" where
  "sortedByM f (x#y#xs) = do {b <- f x y; b' <- sortedByM f (y#xs); return (b \<and> b')}" |
  "sortedByM f ([x]) = return True" |
  "sortedByM f ([]) = return True"


definition sortBy :: "('b \<Rightarrow> 'b \<Rightarrow> (bool, 'a) cont) \<Rightarrow> 'b list \<Rightarrow> ('b list, 'a) cont" where
  "sortBy P xs \<equiv> do {
    ys \<leftarrow> select {ys. List.set ys = List.set xs};
    sorted \<leftarrow> sortedByM P ys;
    if sorted then return ys else todo
}"

abbreviation (input) lex_ord where
  "lex_ord x y \<equiv> fst x \<le> fst y \<and> (fst y \<le> fst x \<longrightarrow> snd x \<le> snd y)"

(* Hard to write this without mutating while iterating without substantially diverging from
   the spec, as initiate_validator_exit does a whole bunch of reads & writes *)
definition process_registry_updates ::
  "(unit, 'a) cont"
where
  "process_registry_updates \<equiv> do {
    vals \<leftarrow> read validators;
    _ \<leftarrow> forM (enumerate (var_list_inner vals))
      ((\<lambda>(index, val). do {
        current_epoch \<leftarrow> get_current_epoch;
        val \<leftarrow> (if is_eligible_for_activation_queue val then do {
                      x \<leftarrow> current_epoch .+ Epoch 1;
                      return (val\<lparr>activation_eligibility_epoch_f := x\<rparr>)}
                 else return val);
        _ \<leftarrow> update_validator val index;           
        _ \<leftarrow> when (is_active_validator val current_epoch \<and>
                effective_balance_f val \<le> EJECTION_BALANCE config) 
               (initiate_validator_exit index);
          return ()
    }));
    vals \<leftarrow> read validators;
    potential_activation_queue \<leftarrow> filterM (\<lambda>(index,val). is_eligible_for_activation val) 
                                           (enumerate (var_list_inner vals));
    let activation_queue = map fst potential_activation_queue;  
    activation_queue \<leftarrow> sortBy (\<lambda>index index'. do {
                                vals \<leftarrow> read validators;
                                val  \<leftarrow> var_list_index vals index;
                                val' \<leftarrow> var_list_index vals index';
                                let epoch  = activation_eligibility_epoch_f val;
                                let epoch' = activation_eligibility_epoch_f val';   
                                return (lex_ord ( epoch, index)  ( epoch', index'))}) activation_queue;
  churn_limit \<leftarrow> get_validator_churn_limit;
    _ \<leftarrow> forM (take (u64_to_nat churn_limit) activation_queue) (\<lambda>index. do {
       vals \<leftarrow> read validators;
       val  \<leftarrow> var_list_index vals index;
       current_epoch \<leftarrow> get_current_epoch;
       active_epoch \<leftarrow> compute_activation_exit_epoch current_epoch;
       update_validator (val\<lparr>activation_epoch_f := active_epoch\<rparr>) index 
    });
    write_to validators ( vals)
  }"

definition process_historical_summaries_update :: "(unit, 'a) cont" where
  "process_historical_summaries_update \<equiv> do {
    current_epoch \<leftarrow> get_current_epoch;
    next_epoch \<leftarrow> current_epoch .+ Epoch 1;
    modulus \<leftarrow> word_unsigned_div (SLOTS_PER_HISTORICAL_ROOT config) (SLOTS_PER_EPOCH config);
    next_epoch_offset \<leftarrow> epoch_to_u64 next_epoch .% modulus;
    when (next_epoch_offset = 0)
      (do {
        block_roots_list \<leftarrow> read block_roots;
        state_roots_list \<leftarrow> read state_roots;
        let historical_summary = \<lparr>
          block_summary_root_f = hash_tree_root block_roots_list,
          state_summary_root_f = hash_tree_root state_roots_list
        \<rparr>;
        old_historical_summaries \<leftarrow> read historical_summaries;
        let new_historical_summaries = var_list_inner old_historical_summaries @ [historical_summary];
        write_to historical_summaries (VariableList new_historical_summaries)
      })
  }"

definition "get_validator index = do {
  vals \<leftarrow> read validators;
  var_list_index vals index
}"

definition eth_aggregate_pubkeys :: "PublicKey list \<Rightarrow> (PublicKey, 'a) cont"
  where
  "eth_aggregate_pubkeys pubkeys = undefined"

(* Verifying the random selection works correctly is well out of scope of the project, so we just take 
   a non-deterministic selection over all possible results *)
definition get_next_sync_committee_indices :: "(u64 list, 'a) cont" where
 "get_next_sync_committee_indices \<equiv> do {
   current_epoch <- get_current_epoch;
   epoch \<leftarrow> current_epoch .+ Epoch 1;
   active_validator_indices \<leftarrow> get_active_validator_indices epoch;
   sync_committee_indices \<leftarrow> select {xs. List.set xs \<subseteq> List.set active_validator_indices \<and>
                                         length xs = unat (SYNC_COMMITTEE_SIZE config)};
   return sync_committee_indices}
"

definition get_next_sync_committee :: "(SyncCommittee, 'a) cont"
  where "get_next_sync_committee = do {
    indices \<leftarrow> get_next_sync_committee_indices;
    validators \<leftarrow> mapM get_validator indices;
    let pubkeys = map pubkey_f validators;
    aggregate_pubkey \<leftarrow> eth_aggregate_pubkeys pubkeys;
    return (SyncCommittee.make (Vector pubkeys) aggregate_pubkey )
}"

definition process_sync_committee_updates :: "(unit, 'a) cont" 
  where "process_sync_committee_updates \<equiv> do {
     current_epoch \<leftarrow> get_current_epoch;
     next_epoch    \<leftarrow> current_epoch .+ Epoch 1;
     x             \<leftarrow> epoch_to_u64 next_epoch .% EPOCHS_PER_SYNC_COMMITTEE_PERIOD;
     when (x = 0) (do {
        current_next_sync_committee \<leftarrow> read next_sync_committee;
        _ \<leftarrow> write_to current_sync_committee current_next_sync_committee;
        new_next_sync_committee \<leftarrow> get_next_sync_committee;
        write_to next_sync_committee new_next_sync_committee
   })
}"

definition process_participation_flag_updates :: "(unit, 'a) cont" where
  "process_participation_flag_updates \<equiv> do {
    old_current_epoch_participation \<leftarrow> read current_epoch_participation;
    _ \<leftarrow> write_to previous_epoch_participation old_current_epoch_participation;
    vals \<leftarrow> read validators;
    let num_validators = (length (var_list_inner vals));
    let new_current_epoch_participation = List.replicate num_validators (ParticipationFlags [False, False, False]);
    write_to current_epoch_participation (VariableList new_current_epoch_participation)
  }"

definition process_epoch :: "(unit, 'a) cont" where
  "process_epoch \<equiv> do {
    _ \<leftarrow> process_justification_and_finalization;
    _ \<leftarrow> process_inactivity_updates;
    _ \<leftarrow> process_rewards_and_penalties;
    _ \<leftarrow> process_registry_updates;
    _ \<leftarrow> process_slashings;
    _ \<leftarrow> process_eth1_data_reset;
    _ \<leftarrow> process_effective_balance_updates;
    _ \<leftarrow> process_slashings_reset;
    _ \<leftarrow> process_randao_mixes_reset;
    _ \<leftarrow> process_historical_summaries_update;
    _ \<leftarrow> process_participation_flag_updates;
    _ \<leftarrow> process_sync_committee_updates;
    return ()
  }"

end

end