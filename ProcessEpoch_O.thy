theory ProcessEpoch_O
imports Hoare_Logic ProcessEpoch
begin

record ProgressiveBalancesCache = 
   total_active_balance_f :: u64
   previous_epoch_flag_attesting_balances_f :: "u64 list"
   current_epoch_flag_attesting_balances_f ::  "u64 list"

record ActivationQueue =
   eligible_validators_f :: "(Epoch \<times> u64) list"

record BaseRewardsCache = 
  effective_balances_f :: "u64 list"
  base_rewards_f :: "u64 list"

record SlashingsContext = 
    adjusted_total_slashing_balance_f :: "u64"
    target_withdrawable_epoch_f :: Epoch


record ExitCache =
    exit_epoch_counts_f :: "Epoch \<rightharpoonup> u64"

record StateContext =
    current_epoch_f :: Epoch
    next_epoch_f :: Epoch
    is_in_inactivity_leak_f :: bool
    churn_limit_f :: u64

record RewardsAndPenaltiesContext =
    unslashed_participating_increments_array_f :: "u64 list"
    active_increments_f :: "u64"

record ValidatorInfo =
    index_f :: u64
    effective_balance_f :: u64
    base_reward_f :: u64
    is_eligible_f :: bool
    is_slashed_f :: bool
    is_active_current_epoch_f :: bool
    is_active_previous_epoch_f :: bool
    previous_epoch_participation_f :: ParticipationFlags
    current_epoch_participation_f :: ParticipationFlags

record EffectiveBalancesContext = 
    downward_threshold_f ::  u64
    upward_threshold_f :: u64

type_synonym ('e, 'addr) ref = "((BeaconState \<times> ('addr \<Rightarrow> 'addr heap_value option)), 'e option) lens"



definition "exit_epoch :: (Validator, Epoch) lens \<equiv> Lens exit_epoch_f (\<lambda>v e. v\<lparr>exit_epoch_f := e\<rparr>) (\<lambda>_. True)"
definition "withdrawable_epoch :: (Validator, Epoch) lens \<equiv> Lens withdrawable_epoch_f (\<lambda>v e. v\<lparr>withdrawable_epoch_f := e\<rparr>) (\<lambda>_. True)"

definition "activation_epoch :: (Validator, Epoch) lens \<equiv>
             Lens activation_epoch_f (\<lambda>v e. v\<lparr>activation_epoch_f := e\<rparr>) (\<lambda>_. True)"
locale extended_vc = verified_con  + hoare_logic +
  fixes "progressive_balances_cache" :: "(ProgressiveBalancesCache, 'b) ref" 
  fixes "activation_queue" :: "(ActivationQueue, 'b) ref" 
  fixes "state_context" :: "(StateContext, 'b) ref"
  fixes "exit_cache" :: "(ExitCache, 'b) ref"
  fixes "base_rewards_cache" :: "(BaseRewardsCache, 'b) ref"
  fixes "num_active_validators" :: "(u64, 'b) ref"

  assumes valid_pbc[simp]: "valid_lens progressive_balances_cache"
  assumes valid_ac[simp]:  "valid_lens activation_queue"
  assumes valid_sc[simp]:  "valid_lens state_context"
  assumes valid_ec[simp]:  "valid_lens exit_cache"
  assumes valid_brc[simp]: "valid_lens base_rewards_cache"
  assumes valid_nav[simp]: "valid_lens num_active_validators"



context verified_con begin

definition "abstract R f = spec R ; f ()"

definition "grab S = do {
  _ <- assertion (\<lambda>_. S \<noteq> {});
  angel S 
}"


definition "singleton_p f \<equiv> Abs_p_set (Pair {id, f} f)"


lemma set_of_singleton [simp]: "set_of (singleton_p f) = {id, f}" 
  apply (clarsimp simp: set_of_def singleton_p_def)
  by (subst Abs_p_set_inverse; clarsimp)

lemma point_of_singleton [simp]: "point_of (singleton_p f) = f" 
  apply (clarsimp simp: point_of_def singleton_p_def)
  by (subst Abs_p_set_inverse; clarsimp)

term "(\<lambda>s. grab {(l, s').  ((maps_to l v -* eq (singleton_p (K s)))) s'}) "


end



context hoare_logic begin

lemma drop_resource: "lift (maps_to l v \<and>* Q) s \<Longrightarrow> lift Q s"
  apply (clarsimp simp: lift_def)
  apply (clarsimp simp: sep_conj_def point_of_plus_domain_iff)
  apply (rule_tac x=y in exI, clarsimp)
  apply (clarsimp simp: maps_point_simp)
  apply (subgoal_tac "get l s = Some v")
   apply (subgoal_tac "get l (point_of y s) = Some v")
  apply (clarsimp simp: sep_disj_p_set_def)
    apply (metis maps_to_def set_get_def valid_lens_def)
  apply (clarsimp simp: sep_disj_p_set_def)
   apply (smt (verit, ccfv_threshold) comp_eq_elim disj_cylindric_set_def maps_to_def point_in_set set_get_def valid_lens_def)
  by (metis get_set_def maps_to_def valid_lens_def)


lemma "hoare_triple (ALLS l. lift (maps_to l v \<longrightarrow>* R)) (alloc v) (lift R)"
  apply (clarsimp simp: alloc_def hoare_triple_def run_def)
  apply (rule Inf_lower2)
  apply (clarsimp simp: image_iff)
   apply (rule_tac x="\<lambda>_. R" in exI)
   apply (rule refl)
  apply (subst Sup_le_iff, clarsimp)
  by (metis (no_types, lifting) Collect_mono assert_iso seq_mono_left)

lemma all_liftD: "lift (ALLS x. P x) s \<Longrightarrow> (ALLS x. lift (P x)) s"
  apply ( clarsimp simp: lift_def)
  apply (blast)
  done

lemma alloc_wp[wp]:"(\<And>l. hoare_triple (lift (P l)) (c l) Q) \<Longrightarrow>  hoare_triple (lift (ALLS l.  (maps_to l v \<longrightarrow>* (P l)))) (bindCont (alloc v) c) (Q)"
  apply (clarsimp simp: alloc_def hoare_triple_def run_def bindCont_def)
  apply (rule Inf_lower2)
  apply (clarsimp simp: image_iff)
   apply (rule_tac x="P" in exI)
   apply (rule refl)
  apply (subst Sup_le_iff, clarsimp)
  apply (rule order_trans)
   apply (rule seq_mono_right)
   apply (assumption)
  apply (rule order_trans)
   apply (rule hoare_chain')
   apply (rule order_refl)
  apply (rule seq_mono_left)
  apply (subst assert_iso[symmetric])
  apply (clarsimp)
  apply (drule all_liftD)
  apply (blast)
  done

 
  

end

context extended_vc

begin

definition "saturating_sub x y \<equiv> if x \<ge> y then x - y else 0"

text \<open>definition "maps_to x y \<equiv> \<lambda>s. snd s = [x \<mapsto> y]"

term "(maps_to addr (list [ptr total_active_balance,
                           ptr previous_epoch_flag_attesting_balances,
                           ptr current_epoch_flag_attesting_balances]) \<and>*  maps_to total_active_balance (u64 (total_active_balance_f cache)))"\<close>


text \<open>definition "translate_ProgressiveBalancesCache" :: 
    "'b \<Rightarrow> ProgressiveBalancesCache \<Rightarrow> ('e :: stronger_sep_algebra \<times> ('b \<Rightarrow> 'b heap_value option) \<Rightarrow> bool)"
where "translate_ProgressiveBalancesCache addr cache \<equiv> \<lambda>s.
        \<exists>total_active_balance previous_epoch_flag_attesting_balances
         current_epoch_flag_attesting_balances.
         (maps_to addr (list [ptr total_active_balance,
                           ptr previous_epoch_flag_attesting_balances,
                           ptr current_epoch_flag_attesting_balances]) \<and>*
          maps_to total_active_balance (u64 (total_active_balance_f cache)) \<and>* 
          maps_to previous_epoch_flag_attesting_balances ((list o map u64 o previous_epoch_flag_attesting_balances_f) cache) \<and>*
          maps_to current_epoch_flag_attesting_balances ((list o map u64 o current_epoch_flag_attesting_balances_f) cache)) s"

definition "translate_ExitCache" :: 
    "'b \<Rightarrow> ExitCache \<Rightarrow> ('e :: stronger_sep_algebra \<times> ('b \<Rightarrow> 'b heap_value option) \<Rightarrow> bool)"
where "translate_ExitCache addr cache \<equiv> \<lambda>s.
        (maps_to addr ((list o map u64 o exit_epoch_counts_f) cache)) s"


definition "translate_ActivationQueue" :: 
    "'b \<Rightarrow> ActivationQueue \<Rightarrow> ('e :: stronger_sep_algebra \<times> ('b \<Rightarrow> 'b heap_value option) \<Rightarrow> bool)"
    where "translate_ActivationQueue addr queue \<equiv> 
         maps_to addr (list (map (\<lambda>x. list [(u64 o raw_epoch o fst) x, u64 (snd x)]) (eligible_validators_f queue)  ))"


definition "translate_BaseRewardsCache" :: 
    "'b \<Rightarrow> BaseRewardsCache \<Rightarrow> ('e :: stronger_sep_algebra \<times> ('b \<Rightarrow> 'b heap_value option) \<Rightarrow> bool)"
    where "translate_BaseRewardsCache addr cache \<equiv> \<lambda>s.
          \<exists>effective_balances base_rewards.
         (maps_to addr (list [ptr effective_balances,
                           ptr base_rewards]) \<and>*
          maps_to effective_balances ((list o map u64 o effective_balances_f) cache) \<and>*
          maps_to base_rewards ((list o map u64 o base_rewards_f) cache)) s"
\<close>
text 
\<open>def new_exit_cache(state: BeaconState) -> ExitCache:
    exit_cache = ExitCache(exit_epoch_counts={})
    for validator in state.validators:
        if validator.exit_epoch != FAR_FUTURE_EPOCH:
            record_validator_exit(exit_cache, validator.exit_epoch)
    return exit_cache
\<close>

text 
\<open>
def record_validator_exit(exit_cache: ExitCache, exit_epoch: Epoch):
    if exit_epoch in exit_cache.exit_epoch_counts:
        exit_cache.exit_epoch_counts[exit_epoch] += 1
    else:
        exit_cache.exit_epoch_counts[exit_epoch] = 1
\<close>

definition record_validator_exit :: "(ExitCache, 'b) ref \<Rightarrow> Epoch \<Rightarrow> (unit, 'a) cont"
  where "record_validator_exit ec ee \<equiv> do {
   cache <- exit_epoch_counts_f <$> read ec;
   if ee \<in> dom cache then do {
        x <- the (cache ee) .+ 1;
        let cache = cache(ee \<mapsto> x);
        ec := return (ec\<lparr> exit_epoch_counts_f := cache \<rparr>)
   } else do {
     let cache = cache(ee \<mapsto> 1);
     ec := return (ec\<lparr>exit_epoch_counts_f := cache \<rparr>)
   }
}"

definition new_exit_cache :: "(ExitCache, 'a) cont"
  where "new_exit_cache \<equiv> do {
   vs <- read validators; 
   let epochs = map exit_epoch_f (var_list_inner vs);
   let frequency = of_nat o count_list epochs;
   return (ExitCache.fields (\<lambda>e. if frequency e = 0 then None else Some (frequency e) ))
}"

text \<open>def get_max_exit_epoch(exit_cache: ExitCache) -> Epoch:
    if len(exit_cache.exit_epoch_counts) == 0:
        return 0
    else:
        return max(exit_cache.exit_epoch_counts.keys())\<close>

definition get_max_exit_epoch :: "ExitCache \<Rightarrow> Epoch"
  where "get_max_exit_epoch cache = (let counts = dom (exit_epoch_counts_f cache) in if finite counts \<and> counts \<noteq> {} then Max counts else Epoch 0) " 

text \<open>def get_exit_queue_churn(exit_cache: ExitCache, exit_queue_epoch: Epoch) -> uint64:
    return exit_cache.exit_epoch_counts.get(exit_queue_epoch) or 0\<close>

definition get_exit_queue_churn :: "ExitCache \<Rightarrow> Epoch \<Rightarrow> u64"
  where "get_exit_queue_churn cache epoch = case_option 0 id (exit_epoch_counts_f cache epoch)"

notation liftM (infixl "<$>" 50)



definition initiate_validator_exit_fast :: "(Validator, 'b) ref \<Rightarrow> (ExitCache, 'b) ref \<Rightarrow> StateContext \<Rightarrow> (unit, 'a) cont"
  where "initiate_validator_exit_fast validator ec state_ctxt = do{
   let exit_epoch = mut (exit_epoch |o> validator);
   let withdrawable_epoch = mut (withdrawable_epoch |o> validator);
   ee <- read exit_epoch;
   exit_cache <- read ec;     
   _ <- when (ee = FAR_FUTURE_EPOCH) (do {
        let max_exit_epoch_from_cache = get_max_exit_epoch(exit_cache);
        activation_exit_epoch \<leftarrow> (compute_activation_exit_epoch (current_epoch_f state_ctxt));
        let exit_queue_epoch = max max_exit_epoch_from_cache activation_exit_epoch;
        let exit_queue_churn = get_exit_queue_churn exit_cache exit_queue_epoch;
        exit_queue_epoch <- (if exit_queue_churn \<ge> churn_limit_f state_ctxt then exit_queue_epoch .+ Epoch 1 else return exit_queue_epoch);
        _  <- (exit_epoch :=  return exit_queue_epoch);
        ee <- read exit_epoch;
        _  <- (withdrawable_epoch := ee .+ Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) );
        _  <- record_validator_exit ec exit_queue_epoch;
        return () });
   return ()}"


text \<open>def initiate_validator_exit_fast(
    validator: Validator, exit_cache: ExitCache, state_ctxt: StateContext
):
    # Return if validator already initiated exit
    if validator.exit_epoch != FAR_FUTURE_EPOCH:
        return

    # Compute exit queue epoch
    max_exit_epoch_from_cache = get_max_exit_epoch(exit_cache)
    exit_queue_epoch = max(
        max_exit_epoch_from_cache,
        compute_activation_exit_epoch(state_ctxt.current_epoch),
    )
    exit_queue_churn = get_exit_queue_churn(exit_cache, exit_queue_epoch)
    if exit_queue_churn >= state_ctxt.churn_limit:
        exit_queue_epoch += Epoch(1)

    # Set validator exit epoch and withdrawable epoch
    validator.exit_epoch = exit_queue_epoch
    validator.withdrawable_epoch = Epoch(
        validator.exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY
    )

    # Update cache
    record_validator_exit(exit_cache, exit_queue_epoch)\<close>

definition "read_ProgressiveBalancesCache" :: 
  "'b \<Rightarrow> (ProgressiveBalancesCache, 'a) cont"
  where "read_ProgressiveBalancesCache root_addr \<equiv> do {
        ptrs \<leftarrow> read root_addr;
        total_active_balance_ptr \<leftarrow>  index_ptr_from_list ptrs 0;
        previous_epoch_flag_attesting_balances_ptr \<leftarrow> index_ptr_from_list ptrs 1;
        current_epoch_flag_attesting_balances_ptr \<leftarrow>  index_ptr_from_list ptrs 2;
        (total_active_balance :: u64) \<leftarrow> read total_active_balance_ptr;
        (previous_epoch_flag_attesting_balances :: 'b heap_value list) \<leftarrow> read previous_epoch_flag_attesting_balances_ptr;
        (previous_epoch_flag_attesting_balances :: u64 list) \<leftarrow> mapM (lift_option o u64_of) previous_epoch_flag_attesting_balances;
        (current_epoch_flag_attesting_balances_ptr :: 'b heap_value list) \<leftarrow> read current_epoch_flag_attesting_balances_ptr;
        (current_epoch_flag_attesting_balances_ptr :: u64 list) \<leftarrow> mapM (lift_option o u64_of) current_epoch_flag_attesting_balances_ptr;
         return
            (ProgressiveBalancesCache.fields
                total_active_balance 
                previous_epoch_flag_attesting_balances
                current_epoch_flag_attesting_balances_ptr)
}"


definition "write_ProgressiveBalancesCache" :: 
  "'b \<Rightarrow> ProgressiveBalancesCache \<Rightarrow> (unit, 'a) cont"
  where "write_ProgressiveBalancesCache root_addr pbc \<equiv> do {
        ptrs \<leftarrow> read root_addr;
        total_active_balance_ptr \<leftarrow>  index_ptr_from_list ptrs 0;
        previous_epoch_flag_attesting_balances_ptr \<leftarrow> index_ptr_from_list ptrs 1;
        current_epoch_flag_attesting_balances_ptr \<leftarrow>  index_ptr_from_list ptrs 2;
        _ \<leftarrow> write_to total_active_balance_ptr (total_active_balance_f pbc);
        _ \<leftarrow> write_to previous_epoch_flag_attesting_balances_ptr (map u64 (previous_epoch_flag_attesting_balances_f pbc)) ;
        _ \<leftarrow> write_to current_epoch_flag_attesting_balances_ptr (map u64 (current_epoch_flag_attesting_balances_f pbc)) ;
        return ()
}"


definition "read_BaseRewardsCache" :: 
  "'b \<Rightarrow> (BaseRewardsCache, 'a) cont"
  where "read_BaseRewardsCache root_addr \<equiv> do {
        ptrs \<leftarrow> read root_addr;
        effective_balances_ptr \<leftarrow>  index_ptr_from_list ptrs 0;
        base_rewards_ptr \<leftarrow> index_ptr_from_list ptrs 1;
        (effective_balances :: 'b heap_value list) \<leftarrow> read effective_balances_ptr;
        (effective_balances :: u64 list) \<leftarrow> mapM (lift_option o u64_of) effective_balances;
        (base_rewards :: 'b heap_value list) \<leftarrow> read base_rewards_ptr;
        (base_rewards :: u64 list) \<leftarrow> mapM (lift_option o u64_of) base_rewards;
         return
            (BaseRewardsCache.fields
                effective_balances 
                base_rewards)
}"


definition get_cached_base_reward :: "BaseRewardsCache \<Rightarrow> u64 => (u64, 'a) cont" 
  where "get_cached_base_reward cache index  = do {
    _ <- assertion (\<lambda>s. index < of_nat (length (effective_balances_f cache)));
    effective_balance_eth <- word_unsigned_div (effective_balances_f cache ! unat index) (EFFECTIVE_BALANCE_INCREMENT config); 
    _ <- assertion (\<lambda>s. effective_balance_eth < of_nat (length (base_rewards_f cache)));
    return (base_rewards_f cache ! unat effective_balance_eth)
}"


definition get_base_reward_per_increment_fast :: "ProgressiveBalancesCache \<Rightarrow> (u64, 'a) cont"
  where "get_base_reward_per_increment_fast progressive_balances = do {
        x <- EFFECTIVE_BALANCE_INCREMENT config .* BASE_REWARD_FACTOR config;
        y <- integer_squareroot (total_active_balance_f progressive_balances);
        word_unsigned_div x y    
}"


definition get_base_reward_fast :: "u64 \<Rightarrow> ProgressiveBalancesCache \<Rightarrow> (u64, 'a) cont"
  where "get_base_reward_fast effective_balance progressive_balances = do {
    increments <- word_unsigned_div effective_balance (EFFECTIVE_BALANCE_INCREMENT config);
    base_reward_per_increment <- get_base_reward_per_increment_fast progressive_balances;
    increments .* base_reward_per_increment
}"



definition compute_base_rewards :: "(u64 list, 'a) cont" 
  where "compute_base_rewards = do {
   pbc <- read_beacon progressive_balances_cache;
   max_balance <- MAX_EFFECTIVE_BALANCE  .+ EFFECTIVE_BALANCE_INCREMENT config;
   xs <- forM (range 0 (unat max_balance) (unat (EFFECTIVE_BALANCE_INCREMENT config))) (\<lambda>effective_balance. get_base_reward_fast (of_nat effective_balance) pbc);
   return (xs :: u64 list)
}"


definition process_single_slashing :: "u64 \<Rightarrow> Validator \<Rightarrow> SlashingsContext \<Rightarrow> ProgressiveBalancesCache \<Rightarrow> (u64, 'a) cont"
  where "process_single_slashing balance validator s_ctxt pbc = do {
                  let slashed = Validator.slashed_f validator;
                  if (slashed \<and> target_withdrawable_epoch_f s_ctxt = withdrawable_epoch_f validator)
                      then do {
                           let increment = EFFECTIVE_BALANCE_INCREMENT config;
                           penalty_numerator <- word_unsigned_div (Validator.effective_balance_f validator) increment;
                           penalty_numerator <- penalty_numerator .* adjusted_total_slashing_balance_f s_ctxt;
                           penalty <- word_unsigned_div penalty_numerator (total_active_balance_f pbc);
                           penalty <- penalty .* increment;
                           return (saturating_sub balance penalty)
                      }
                      else do {return balance}
}"

text \<open>*
    balance: Gwei,
    validator: Validator,
    slashings_ctxt: SlashingsContext,
    progressive_balances: ProgressiveBalancesCache,
) -> Gwei:
    if (
        validator.slashed
        and slashings_ctxt.target_withdrawable_epoch == validator.withdrawable_epoch
    ):
        increment = EFFECTIVE_BALANCE_INCREMENT
        penalty_numerator = (
            validator.effective_balance
            // increment
            * slashings_ctxt.adjusted_total_slashing_balance
        )
        penalty = (
            penalty_numerator // progressive_balances.total_active_balance * increment
        )
        return saturating_sub(balance, penalty)
    else:
        return balance
*\<close>


definition "read_ActivationQueue" :: 
    "'b \<Rightarrow> (ActivationQueue, 'a) cont"
    where "read_ActivationQueue addr \<equiv> do {
         (queue :: 'b heap_value list) <- read_list addr;
         queue' <- forM queue (\<lambda>v. do {
              pair    <- lift_option (list_of v); 
              epoch   <- index_u64_from_list pair 0;
              v_index <- index_u64_from_list pair 1;
              return (Epoch epoch, v_index)
         });
         return (ActivationQueue.fields queue')
}"

definition "could_be_eligible_for_activation_at" :: "Validator \<Rightarrow> Epoch \<Rightarrow> bool"
  where "could_be_eligible_for_activation_at v e \<equiv>
        activation_eligibility_epoch_f v < e \<and> activation_epoch_f v = FAR_FUTURE_EPOCH"

definition add_if_could_be_eligible_for_activation :: "ActivationQueue \<Rightarrow> u64 \<Rightarrow> Validator \<Rightarrow> Epoch \<Rightarrow> ActivationQueue"
  where "add_if_could_be_eligible_for_activation q i v e \<equiv> if could_be_eligible_for_activation_at v e 
                                                             then ( q\<lparr>eligible_validators_f := (activation_eligibility_epoch_f v, i) # eligible_validators_f q\<rparr>)
                                                             else q"


definition new_activation_queue :: "(ActivationQueue, 'a) cont"
  where "new_activation_queue = do {
         current_epoch <- get_current_epoch;
         next_epoch    <- current_epoch .+ (Epoch 1);
         validators <- read validators;
         let queue = fold (\<lambda>(i, v) q. add_if_could_be_eligible_for_activation q i v next_epoch) (enumerate (var_list_inner validators)) (ActivationQueue.fields []);
         return queue }"


text \<open>def get_validators_eligible_for_activation(
    activation_queue: ActivationQueue,
    finalized_epoch: Epoch,
    churn_limit: uint64,
) -> [ValidatorIndex]:
    return [
        index for (eligibility_epoch, index) in activation_queue.eligible_validators
        if eligibility_epoch <= finalized_epoch
    ][:churn_limit]\<close>

definition get_validators_eligible_for_activation :: "ActivationQueue \<Rightarrow> Epoch \<Rightarrow> u64 \<Rightarrow> u64 list"
  where "get_validators_eligible_for_activation queue final_epoch churn_limit \<equiv> 
  take (unat churn_limit) (map snd (filter (\<lambda>(eligibility_epoch, index). eligibility_epoch \<le> final_epoch) (eligible_validators_f queue) ))"


text \<open>for flag_index in range(len(participation_flag_weights)):
        if has_flag(current_epoch_participation, flag_index):
            if new_effective_balance > old_effective_balance:
                next_epoch_progressive_balances.previous_epoch_flag_attesting_balances[
                    flag_index
                ] += (new_effective_balance - old_effective_balance)
            else:
                next_epoch_progressive_balances.previous_epoch_flag_attesting_balances[
                    flag_index
                ] -= (old_effective_balance - new_effective_balance)
\<close>

text \<open>def new_next_epoch_progressive_balances(
    progressive_balances: ProgressiveBalancesCache,
) -> ProgressiveBalancesCache:
    # Set total active balance to 0, it will be updated in
    # `process_single_effective_balance_update`.
    total_active_balance = 0

    # Rotate current epoch to previous, and initialize current to 0.
    previous_epoch_flag_attesting_balances = (
        progressive_balances.current_epoch_flag_attesting_balances
    )
    current_epoch_flag_attesting_balances = [0, 0, 0]

    return ProgressiveBalancesCache(
        total_active_balance=total_active_balance,
        previous_epoch_flag_attesting_balances=previous_epoch_flag_attesting_balances,
        current_epoch_flag_attesting_balances=current_epoch_flag_attesting_balances,
    )\<close>


definition "new_next_epoch_progressive_balance" :: "ProgressiveBalancesCache \<Rightarrow> ProgressiveBalancesCache"
  where "new_next_epoch_progressive_balance pbc \<equiv> let 
         new_balance = 0;
         new_previous_epoch_flag_attesting_balances = current_epoch_flag_attesting_balances_f pbc;
         new_current_epoch_flag_attesting_balances = [0,0,0] in
         pbc\<lparr>total_active_balance_f := new_balance,
             previous_epoch_flag_attesting_balances_f := new_previous_epoch_flag_attesting_balances,
             current_epoch_flag_attesting_balances_f := new_current_epoch_flag_attesting_balances\<rparr>"

definition update_next_epoch_progressive_balances :: 
  "Epoch \<Rightarrow> (ProgressiveBalancesCache, 'b) ref \<Rightarrow> Validator \<Rightarrow> ParticipationFlags \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where "update_next_epoch_progressive_balances next_epoch next_epoch_progressive_balances
                               validator cep old_effective_balance = do {
                                    let new_effective_balance = Validator.effective_balance_f validator;
                                    total_active_balance <- total_active_balance_f <$> read next_epoch_progressive_balances;
                                    total_active_balance <- if (is_active_validator validator next_epoch) 
                                                                then total_active_balance .+ new_effective_balance
                                                                else return total_active_balance;
                                    _ <- (next_epoch_progressive_balances := return (next_epoch_progressive_balances\<lparr>total_active_balance_f := total_active_balance\<rparr>));
                                    let flag_indexes = range 0 (length (participation_flag_weights cep)) 1; 
                                    _ <- when (\<not> (slashed_f validator)) (do {
                                           xs <- (if (new_effective_balance > old_effective_balance) 
                                                      then do {
                                                            x  <- new_effective_balance .- old_effective_balance;
                                                            xs <- forM flag_indexes (\<lambda>i. do { ys <- previous_epoch_flag_attesting_balances_f <$> read next_epoch_progressive_balances;
                                                                                              if (has_flag cep i) then (word_unsigned_add (ys ! i)  x)
                                                                                                             else (return (ys ! i))});
                                                            return xs}
                                                      else do {
                                                            x <- old_effective_balance .- new_effective_balance;
                                                            xs <- forM flag_indexes (\<lambda>i. do { ys <- previous_epoch_flag_attesting_balances_f <$> read next_epoch_progressive_balances;
                                                                                              if (has_flag cep i) then (ys ! i) .- x
                                                                                                                  else (return (ys ! i ))});
                                                            return xs});                                      
                                         (next_epoch_progressive_balances := return (next_epoch_progressive_balances\<lparr>previous_epoch_flag_attesting_balances_f := xs\<rparr>))
                                          });
                                    return ()
                               }"

text \<open>def update_next_epoch_progressive_balances(
    next_epoch: Epoch,
    next_epoch_progressive_balances: ProgressiveBalancesCache,
    validator: Validator,
    current_epoch_participation: ParticipationFlags,
    old_effective_balance: uint64,
):
    new_effective_balance = validator.effective_balance

    # Update total active balance.
    if is_active_validator(validator, next_epoch):
        next_epoch_progressive_balances.total_active_balance += new_effective_balance

    # Update the current epoch totals which are the *previous* epoch totals in the cache
    # and were computed with the validator's `old_effective_balance`.
    # Slashed validators are not part of the unslashed participating totals.
    if validator.slashed:
        return

    for flag_index in range(len(participation_flag_weights)):
        if has_flag(current_epoch_participation, flag_index):
            if new_effective_balance > old_effective_balance:
                next_epoch_progressive_balances.previous_epoch_flag_attesting_balances[
                    flag_index
                ] += (new_effective_balance - old_effective_balance)
            else:
                next_epoch_progressive_balances.previous_epoch_flag_attesting_balances[
                    flag_index
                ] -= (old_effective_balance - new_effective_balance)\<close>


definition "process_justification_and_finalization_fast" ::  "(unit, 'a) cont"
  where "process_justification_and_finalization_fast \<equiv> do {
     previous_epoch <- get_previous_epoch;
     current_epoch <- get_current_epoch;
     epoch1 \<leftarrow> GENESIS_EPOCH .+ Epoch 1;
    if current_epoch \<le> epoch1 then
      return ()
    else do {
      pbc \<leftarrow> read progressive_balances_cache;
      let (total_active_balance) = total_active_balance_f pbc;
      let (previous_epoch_flag_attesting_balances) = previous_epoch_flag_attesting_balances_f pbc;
      let (previous_target_balance) = previous_epoch_flag_attesting_balances ! (of_nat TIMELY_TARGET_FLAG_INDEX);
      let (current_epoch_flag_attesting_balances) = current_epoch_flag_attesting_balances_f pbc;
      let (current_target_balance) =  current_epoch_flag_attesting_balances ! (of_nat TIMELY_TARGET_FLAG_INDEX) ;
      _ \<leftarrow> weigh_justification_and_finalization
         total_active_balance previous_target_balance current_target_balance;
      return ()
      
}}"

definition get_flag_attesting_balance :: "nat \<Rightarrow> Epoch \<Rightarrow> (u64, 'a) cont" 
  where "get_flag_attesting_balance flag_index epoch = do {
   unslashed_participating_indices <- get_unslashed_participating_indices flag_index epoch;
   total_balance <- get_total_balance unslashed_participating_indices;
   return total_balance
}"

text \<open>
def get_flag_attesting_balance(state: BeaconState, flag_index: int, epoch: Epoch) -> Gwei:
    return get_total_balance(state, get_unslashed_participating_indices(state, flag_index, epoch))
\<close>

definition new_progressive_balances :: "(ProgressiveBalancesCache, 'a) cont"
  where  "new_progressive_balances = do {
  total_active_balance <- get_total_active_balance;
  previous_epoch <- get_previous_epoch;
  current_epoch <- get_current_epoch;
  previous_epoch_flag_attesting_balances <- forM [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX, TIMELY_HEAD_FLAG_INDEX] (\<lambda>flag. get_flag_attesting_balance flag previous_epoch);
  current_epoch_flag_attesting_balances <- forM [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX, TIMELY_HEAD_FLAG_INDEX] (\<lambda>flag. get_flag_attesting_balance flag current_epoch);
  return (ProgressiveBalancesCache.fields total_active_balance previous_epoch_flag_attesting_balances
                                          current_epoch_flag_attesting_balances :: ProgressiveBalancesCache)
}"

text \<open>def new_progressive_balances(state: BeaconState) -> ProgressiveBalancesCache:
    total_active_balance = get_total_active_balance(state)
    previous_epoch_flag_attesting_balances = [
        get_flag_attesting_balance(state, TIMELY_SOURCE_FLAG_INDEX, previous_epoch),
        get_flag_attesting_balance(state, TIMELY_TARGET_FLAG_INDEX, previous_epoch),
        get_flag_attesting_balance(state, TIMELY_HEAD_FLAG_INDEX, previous_epoch),
    ]
    current_epoch_flag_attesting_balances = [
        get_flag_attesting_balance(state, TIMELY_SOURCE_FLAG_INDEX, current_epoch),
        get_flag_attesting_balance(state, TIMELY_TARGET_FLAG_INDEX, current_epoch),
        get_flag_attesting_balance(state, TIMELY_HEAD_FLAG_INDEX, current_epoch),
    ]
    return ProgressiveBalancesCache(
        total_active_balance=total_active_balance,
        previous_epoch_flag_attesting_balances=previous_epoch_flag_attesting_balances,
        current_epoch_flag_attesting_balances=current_epoch_flag_attesting_balances,
    )
\<close>

definition new_base_rewards_cache :: "(BaseRewardsCache, 'a) cont" 
  where "new_base_rewards_cache    = do {
 validators <- read validators;
 let effective_balances = map Validator.effective_balance_f (var_list_inner validators);
 base_rewards <- compute_base_rewards;
 return (\<lparr>effective_balances_f = effective_balances, base_rewards_f = base_rewards\<rparr>)
}"

text \<open>
def new_base_reward_cache(
    state: BeaconState
) -> BaseRewardCache:
    effective_balances = [validator.effective_balance for validator in state.validators]
    base_rewards = compute_base_rewards(state)
    return BaseRewardCache(effective_balances=effective_balances, base_rewards=base_rewards)
\<close>


definition get_validator_churn_limit_fast :: "(u64, 'a) cont" 
  where "get_validator_churn_limit_fast = do {
     num_active_validators <- read num_active_validators;
     churn_limit <- word_unsigned_div num_active_validators (CHURN_LIMIT_QUOTIENT config);
     return (max (MIN_PER_EPOCH_CHURN_LIMIT config) churn_limit)
}"

text \<open>def get_validator_churn_limit_fast(state: BeaconState) -> uint64:
    return max(
        MIN_PER_EPOCH_CHURN_LIMIT, state.num_active_validators // CHURN_LIMIT_QUOTIENT
    )\<close>

definition new_state_context :: "(StateContext, 'a) cont"
  where "new_state_context = do {
    current_epoch <- get_current_epoch;
    next_epoch <- current_epoch .+ (Epoch 1); 
    is_in_inactivity_leak <- is_in_inactivity_leak;
    churn_limit <- get_validator_churn_limit_fast;
    return (StateContext.fields current_epoch next_epoch is_in_inactivity_leak churn_limit)
}"



definition new_slashings_context :: "StateContext \<Rightarrow> ProgressiveBalancesCache \<Rightarrow> (SlashingsContext, 'a) cont"
  where "new_slashings_context state_ctxt pbc = do {

   xs <- read slashings;
   total_slashings  <- safe_sum (vector_inner xs);
   adjusted_total_slashing_balance <- total_slashings .* PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX;
   let total_balance = total_active_balance_f pbc;
   let adjusted_total_slashing_balance = min adjusted_total_slashing_balance total_balance;
   target_withdrawable_epoch <- raw_epoch (current_epoch_f state_ctxt) .+ (EPOCHS_PER_SLASHINGS_VECTOR config);
   target_withdrawable_epoch <- word_unsigned_div target_withdrawable_epoch 2;
   return (SlashingsContext.fields adjusted_total_slashing_balance (Epoch target_withdrawable_epoch))
}"

text \<open>
def new_slashings_context(
    state: BeaconState,
    state_ctxt: StateContext,
) -> SlashingsContext:
    adjusted_total_slashing_balance = min(
        sum(state.slashings) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX, total_balance
    )
    target_withdrawable_epoch = (
        state_ctxt.current_epoch + EPOCHS_PER_SLASHINGS_VECTOR // 2
    )
    return SlashingsContext(
        adjusted_total_slashing_balance=adjusted_total_slashing_balance,
        target_withdrawable_epoch=target_withdrawable_epoch,
    )
\<close>

definition unslashed_participating_increment :: "nat \<Rightarrow> (u64, 'a) cont"
  where "unslashed_participating_increment flag_index = do {
    previous_epoch_flag_attesting_balances <- previous_epoch_flag_attesting_balances_f <$> read progressive_balances_cache;
    _ <- assertion (\<lambda>_. flag_index < length previous_epoch_flag_attesting_balances);
    let unslashed_participating_balance = previous_epoch_flag_attesting_balances ! flag_index;
    unslashed_participating_increment <- word_unsigned_div unslashed_participating_balance (EFFECTIVE_BALANCE_INCREMENT config);  
    return unslashed_participating_increment
}"

text \<open>def unslashed_participating_increment(flag_index) -> Gwei:
    unslashed_participating_balance = (
        progressive_balances.previous_epoch_flag_attesting_balances[flag_index]
    )
    return unslashed_participating_balance // EFFECTIVE_BALANCE_INCREMENT\<close>


definition new_rewards_and_penalties_context :: "ProgressiveBalancesCache \<Rightarrow> (RewardsAndPenaltiesContext, 'a) cont"
  where "new_rewards_and_penalties_context pbc = do {
   unslashed_participating_increments_array <- mapM unslashed_participating_increment (range 0 (unat NUM_FLAG_INDICES) 1);
   let total_active_balance = total_active_balance_f pbc;
   active_increments <- word_unsigned_div  total_active_balance (EFFECTIVE_BALANCE_INCREMENT config);
   return (RewardsAndPenaltiesContext.fields unslashed_participating_increments_array active_increments)
}"

text \<open>def new_rewards_and_penalties_context(
    progressive_balances: ProgressiveBalancesCache,
) -> RewardsAndPenaltiesContext:
    unslashed_participating_increments_array = [
        unslashed_participating_increment(flag_index)
        for flag_index in range(NUM_FLAG_INDICES)
    ]
    active_increments = (
        progressive_balances.total_active_balance // EFFECTIVE_BALANCE_INCREMENT
    )
    return RewardsAndPenaltiesContext(
        unslashed_participating_increments_array=unslashed_participating_increments_array,
        active_increments=active_increments,
    )\<close>

definition new_effective_balances_ctxt :: "(EffectiveBalancesContext, 'a) cont"
  where "new_effective_balances_ctxt = do {
   hysteresis_increment <- word_unsigned_div (EFFECTIVE_BALANCE_INCREMENT config) HYSTERESIS_QUOTIENT;
   downward_threshold   <- hysteresis_increment .* HYSTERESIS_DOWNWARD_MULTIPLIER;
   upward_threshold     <- hysteresis_increment .* HYSTERESIS_UPWARD_MULTIPLIER;
   return (EffectiveBalancesContext.fields downward_threshold upward_threshold)
}"

text \<open>
def new_effective_balances_context() -> EffectiveBalancesContext:
    hysteresis_increment = uint64(EFFECTIVE_BALANCE_INCREMENT // HYSTERESIS_QUOTIENT)
    return EffectiveBalancesContext(
        downward_threshold=hysteresis_increment * HYSTERESIS_DOWNWARD_MULTIPLIER,
        upward_threshold=hysteresis_increment * HYSTERESIS_UPWARD_MULTIPLIER,
    )
\<close>

definition new_next_epoch_progressive_balances :: "ProgressiveBalancesCache \<Rightarrow> (ProgressiveBalancesCache, 'a) cont"
  where "new_next_epoch_progressive_balances progressive_balances = do{
   let total_active_balance = (0 :: u64);
   let previous_epoch_flag_attesting_balances = current_epoch_flag_attesting_balances_f progressive_balances;
   let current_epoch_flag_attesting_balances = ([0,0,0] :: u64 list);
   return (ProgressiveBalancesCache.fields total_active_balance previous_epoch_flag_attesting_balances
                                           current_epoch_flag_attesting_balances)
}"         

text \<open># Set total active balance to 0, it will be updated in
    # `process_single_effective_balance_update`.
    total_active_balance = 0

    # Rotate current epoch to previous, and initialize current to 0.
    previous_epoch_flag_attesting_balances = (
        progressive_balances.current_epoch_flag_attesting_balances
    )
    current_epoch_flag_attesting_balances = [0, 0, 0]

    return ProgressiveBalancesCache(
        total_active_balance=total_active_balance,
        previous_epoch_flag_attesting_balances=previous_epoch_flag_attesting_balances,
        current_epoch_flag_attesting_balances=current_epoch_flag_attesting_balances,
    )\<close>






definition process_single_registry_update :: "(Validator, 'b) ref \<Rightarrow> ValidatorInfo \<Rightarrow> ExitCache \<Rightarrow>
                                               u64 list \<Rightarrow> (ActivationQueue, 'b) ref \<Rightarrow> StateContext \<Rightarrow> (unit, 'a) cont"
  where "process_single_registry_update vref val_info ex_cache aq 
                                         next_epoch_aq state_ctxt \<equiv> do {
      let current_epoch = current_epoch_f state_ctxt;
      validator <- read vref;
      _ <- when (is_eligible_for_activation_queue validator) (do {
                 epoch <- current_epoch .+ (Epoch 1);
                (vref := return (validator\<lparr>activation_eligibility_epoch_f := epoch\<rparr>)) 
            });
      validator <- read vref;
      _ <- when (is_active_validator validator current_epoch \<and> Validator.effective_balance_f validator \<le> EJECTION_BALANCE config) 
                (initiate_validator_exit_fast vref exit_cache state_ctxt);
      _ <- when (index_f val_info \<in> List.set aq) (do {
            let validator_activation_epoch = mut (activation_epoch |o> vref);
            (validator_activation_epoch := compute_activation_exit_epoch current_epoch)
            });
      _ <- (next_epoch_aq := return (add_if_could_be_eligible_for_activation next_epoch_aq (index_f val_info) validator (next_epoch_f state_ctxt)));
      return ()
}"

text \<open>
def process_single_registry_update(
    validator: Validator,
    validator_info: ValidatorInfo,
    exit_cache: ExitCache,
    activation_queue: [ValidatorIndex],
    next_epoch_activation_queue: ActivationQueue,
    state_ctxt: StateContext,
):
    current_epoch = state_ctxt.current_epoch

    if is_eligible_for_activation_queue(validator):
        validator.activation_eligibility_epoch = current_epoch + 1

    if (
        is_active_validator(validator, current_epoch)
        and validator.effective_balance <= EJECTION_BALANCE
    ):
        initiate_validator_exit_fast(validator, exit_cache, state_ctxt)

    if validator_info.index in activation_queue:
        validator.activation_epoch = compute_activation_exit_epoch(current_epoch)

    # Caching: add to speculative activation queue for next epoch.
    add_if_could_be_eligible_for_activation(
        new_activation_queue,
        validator_info.index,
        validator,
        state_ctxt.next_epoch,
    )
\<close>

definition "is_unslashed_participating_index v_info flag_index \<equiv> 
        is_active_previous_epoch_f v_info \<and> 
       \<not>is_slashed_f v_info               \<and>
        has_flag (previous_epoch_participation_f v_info) flag_index"

text \<open>
def is_unslashed_participating_index(
    validator_info: ValidatorInfo, flag_index: int
) -> bool:
    return (
        validator_info.is_active_previous_epoch
        and not validator_info.is_slashed
        and has_flag(validator_info.previous_epoch_participation, flag_index)
    )
\<close>
definition get_flag_index_delta ::
      "ValidatorInfo \<Rightarrow> nat \<Rightarrow> RewardsAndPenaltiesContext \<Rightarrow> 
        StateContext \<Rightarrow> ((u64 \<times> u64), 'a) cont" 
  where "get_flag_index_delta v_info flag_index rewards_ctxt state_ctxt = do{
      let base_reward = base_reward_f v_info;
      let weight = PARTICIPATION_FLAG_WEIGHTS ! flag_index;
      let unslashed_participating_increments = 
            unslashed_participating_increments_array_f rewards_ctxt ! flag_index;
      if (is_unslashed_participating_index v_info flag_index) \<and>
                          \<not>(is_in_inactivity_leak_f state_ctxt) then do {
          x <- base_reward .*  weight;
          reward_numerator   <- x .* unslashed_participating_increments;
          reward_denominator <- active_increments_f rewards_ctxt .* WEIGHT_DENOMINATOR;
          reward             <- word_unsigned_div reward_numerator reward_denominator;
          return (reward,0)}
      else if (flag_index \<noteq> TIMELY_HEAD_FLAG_INDEX) then do {
          penalty_numerator <- base_reward .* weight;
          penalty <- word_unsigned_div penalty_numerator WEIGHT_DENOMINATOR;
          return (0,penalty)
      } else       
      return (0,0)
}"

text \<open>
def get_flag_index_delta(
    validator_info: ValidatorInfo,
    flag_index: int,
    rewards_ctxt: RewardsAndPenaltiesContext,
    state_ctxt: StateContext,
) -> (Gwei, Gwei):
    base_reward = validator_info.base_reward
    weight = PARTICIPATION_FLAG_WEIGHTS[flag_index]
    unslashed_participating_increments = (
        rewards_ctxt.unslashed_participating_increments_array[flag_index]
    )

    if is_unslashed_participating_index(validator_info, flag_index):
        if not state_ctxt.is_in_inactivity_leak:
            reward_numerator = base_reward * weight * unslashed_participating_increments
            reward_denominator = rewards_ctxt.active_increments * WEIGHT_DENOMINATOR
            reward = reward_numerator / reward_denominator
            return (reward, 0)
    elif flag_index != TIMELY_HEAD_FLAG_INDEX:
        penalty = base_reward * weight / WEIGHT_DENOMINATOR
        return (0, penalty)
    return (0, 0)
\<close>

definition "get_inactivity_penalty_delta v_info inactivity_score state_ctxt = do {
   if \<not>(is_unslashed_participating_index v_info TIMELY_TARGET_FLAG_INDEX) then do {
     penalty_numerator <- effective_balance_f v_info .* inactivity_score;
     penalty_denominator <- INACTIVITY_SCORE_BIAS config .* INACTIVITY_PENALTY_QUOTIENT_ALTAIR;
     penalty <- word_unsigned_div penalty_numerator penalty_denominator;
     return (0, penalty)
   } else do {
     return (0, 0)
   }
}"

text \<open>def get_inactivity_penalty_delta(
    validator_info: ValidatorInfo,
    inactivity_score: uint64,
    state_ctxt: StateContext,
) -> (Gwei, Gwei):
    # Implementation note: could abstract over fork's inactivity penalty quotient here
    if not is_unslashed_participating_index(validator_info, TIMELY_TARGET_FLAG_INDEX):
        penalty_numerator = validator_info.effective_balance * inactivity_score
        penalty_denominator = INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX
        penalty = penalty_numerator / penalty_denominator
        return (0, penalty)
    return (0, 0)\<close>

definition ref_unsigned_add :: "(u64, 'b) ref \<Rightarrow> (u64, 'b) ref \<Rightarrow> (u64, 'a) cont" 
  where  "ref_unsigned_add x y \<equiv> do {(x' :: u64) <- read x; (y' :: u64) <- read y;  x' .+ y'}" 

definition ref_unsigned_add_l :: "u64 \<Rightarrow> (u64, 'b) ref \<Rightarrow> (u64, 'a) cont" 
  where  "ref_unsigned_add_l x y \<equiv> do {(y' :: u64) <- read_beacon y;  x .+ y'}" 

definition ref_unsigned_add_r :: "(u64, 'b) ref \<Rightarrow> u64 \<Rightarrow> (u64, 'a) cont" 
  where  "ref_unsigned_add_r x y \<equiv> do {(x' :: u64) <- read_beacon x;  x' .+ y}" 

adhoc_overloading
  unsigned_add ref_unsigned_add ref_unsigned_add_l ref_unsigned_add_r


definition process_single_reward_and_penalty :: 
  "u64 \<Rightarrow> u64 \<Rightarrow> ValidatorInfo \<Rightarrow> RewardsAndPenaltiesContext \<Rightarrow> StateContext \<Rightarrow> (u64, 'a) cont"
  where "process_single_reward_and_penalty balance inactivity_score 
                                           val_info rewards_ctxt state_ctxt \<equiv> do{
        if (is_eligible_f val_info) then do {
           rewards <- alloc (0 :: u64);
           penalties <- alloc (0 :: u64);
           let n = length PARTICIPATION_FLAG_WEIGHTS;
           _ <- forM (range 0 n 1) (\<lambda>flag_index. do {
             (reward,penalty) <- get_flag_index_delta val_info flag_index rewards_ctxt state_ctxt;
             _ <- (rewards := rewards .+ reward);
             (penalties := penalties .+ penalty)
             });
           (reward, penalty) <-  get_inactivity_penalty_delta val_info inactivity_score state_ctxt;
           _ <- (rewards := rewards .+ reward);
           _ <- (penalties := penalties .+ penalty);
           r <- read rewards;
           p <- read penalties;
           (if (r \<noteq> 0 \<or> p \<noteq> 0) then do {
               new_balance <- balance .+ r;
               let new_balance = (if new_balance \<ge> p then new_balance - p else 0);
               _ <- free rewards;
               _ <- free penalties;
               return new_balance
           } else do {
             _ <- free rewards;
             _ <- free penalties;
             return balance
           })
        } else (return balance)
}"
  
 

text \<open>def process_single_reward_and_penalty(
    balance: Gwei,
    inactivity_score: uint64,
    validator_info: ValidatorInfo,
    rewards_ctxt: RewardsAndPenaltiesContext,
    state_ctxt: StateContext,
) -> uint64:
    if not validator_info.is_eligible:
        return balance

    rewards = 0
    penalties = 0

    for flag_index in range(len(PARTICIPATION_FLAG_WEIGHTS)):
        reward, penalty = get_flag_index_delta(
            validator_info, flag_index, rewards_ctxt, state_ctxt
        )
        rewards += reward
        penalties += penalty

    reward, penalty = get_inactivity_penalty_delta(
        validator_info,
        inactivity_score,
        state_ctxt,
    )
    rewards += reward
    penalties += penalty

    if rewards != 0 or penalties != 0:
        new_balance = balance + rewards
        new_balance = saturating_sub(new_balance, penalties)
        return new_balance
    else:
        return balance
\<close>

definition process_single_inactivity_update :: "u64 \<Rightarrow> ValidatorInfo \<Rightarrow> StateContext \<Rightarrow> (u64, 'a) cont"
  where "process_single_inactivity_update inactivity_score val_info state_ctxt = do {
  if \<not>(is_eligible_f val_info) then do {
    return inactivity_score
  } else do {
  let new_inactivity_score = inactivity_score;
  new_inactivity_score <- if (is_unslashed_participating_index val_info TIMELY_TARGET_FLAG_INDEX)
                           then (new_inactivity_score .- (min new_inactivity_score 1))
                           else (new_inactivity_score .+ INACTIVITY_SCORE_BIAS config);
  new_inactivity_score <- if \<not>(is_in_inactivity_leak_f state_ctxt)
                           then (new_inactivity_score .- (min new_inactivity_score (INACTIVITY_SCORE_RECOVERY_RATE config)))
                           else (return new_inactivity_score);
  return new_inactivity_score
}}"


text \<open>def process_single_inactivity_update(
    inactivity_score: uint64,
    validator_info: ValidatorInfo,
    state_ctxt: StateContext,
) -> uint64:
    if not validator_info.is_eligible:
        return inactivity_score

    # Increase inactivity score of inactive validators
    new_inactivity_score = inactivity_score
    if is_unslashed_participating_index(validator_info, TIMELY_TARGET_FLAG_INDEX):
        new_inactivity_score -= min(1, inactivity_score)
    else:
        new_inactivity_score += INACTIVITY_SCORE_BIAS

    # Decrease the inactivity score of all eligible validators during a leak-free epoch
    if not state_ctxt.is_in_inactivity_leak:
        new_inactivity_score -= min(
            INACTIVITY_SCORE_RECOVERY_RATE, new_inactivity_score
        )

    return new_inactivity_score\<close>

text \<open>  \<close>

term current_epoch_participation

definition
  process_single_effective_balance_update :: "(u64, 'b) ref \<Rightarrow> (Validator, 'b) ref \<Rightarrow> ValidatorInfo \<Rightarrow> 
                                             (ProgressiveBalancesCache, 'b) ref \<Rightarrow> (BaseRewardsCache, 'b) ref  \<Rightarrow>
                                             EffectiveBalancesContext \<Rightarrow> StateContext \<Rightarrow>ParticipationFlags \<Rightarrow> (unit, 'a) cont"
  where "process_single_effective_balance_update balance validator 
                   val_info next_epb next_ebrc eb_ctxt state_ctxt cep = do {
  balance <- read_beacon balance;
  ebf     <- Validator.effective_balance_f <$> read_beacon validator;  
  d_threshold <- balance .+ (downward_threshold_f eb_ctxt);
  u_threshold <- ebf .+ (upward_threshold_f eb_ctxt);
  _ <- when (d_threshold < ebf \<or>
             u_threshold < balance) (do {
         x <- word_unsigned_mod balance (EFFECTIVE_BALANCE_INCREMENT config);
         new_balance <- balance .- x;
         (validator := return (validator\<lparr> Validator.effective_balance_f := min new_balance MAX_EFFECTIVE_BALANCE\<rparr>))
        });
  val <- read_beacon validator; 
  _ <- update_next_epoch_progressive_balances (next_epoch_f state_ctxt) next_epb val cep (effective_balance_f val_info);
  ebf     <- Validator.effective_balance_f <$> read_beacon validator;  
  (next_ebrc := return (next_ebrc\<lparr>effective_balances_f := effective_balances_f next_ebrc @ [ebf]\<rparr>))
}"

text \<open>def process_single_effective_balance_update(
    balance: Gwei,
    validator: Validator,
    validator_info: ValidatorInfo,
    next_epoch_progressive_balances: ProgressiveBalancesCache,
    next_epoch_base_reward_cache: BaseRewardCache,
    eb_ctxt: EffectiveBalancesContext,
    state_ctxt: StateContext,
):
    # Compute the effective balance change.
    balance = state.balances[index]
    if (
        balance + eb_ctxt.downward_threshold < validator.effective_balance
        or validator.effective_balance + eb_ctxt.upward_threshold < balance
    ):
        validator.effective_balance = min(
            balance - balance % EFFECTIVE_BALANCE_INCREMENT, MAX_EFFECTIVE_BALANCE
        )

    # Update the progressive balances cache for the next epoch.
    update_next_epoch_progressive_balances(
        state_ctxt.next_epoch,
        next_epoch_progressive_balances,
        validator,
        current_epoch_participation,
        validator_info.effective_balance,
    )
    # Add the validator's effective balance to the base reward cache.
    next_epoch_base_reward_cache.effective_balances.append(validator.effective_balance)\<close>

(* definition "is_active_next_epoch (validator :: Validator) (epoch :: Epoch) = (undefined :: bool)"*)

definition process_epoch_single_pass :: "(unit, 'a) cont" 
  where "process_epoch_single_pass = do {
  progressive_balances <- read progressive_balances_cache;
  state_ctxt <- new_state_context;
  slashings_ctxt <- new_slashings_context state_ctxt progressive_balances ;
  rewards_ctxt <- new_rewards_and_penalties_context progressive_balances;
  effective_balances_ctxt <- new_effective_balances_ctxt;
  next_epoch_progressive_balances <- new_next_epoch_progressive_balances progressive_balances;
  nepb <- alloc next_epoch_progressive_balances;
  aq <- read activation_queue; 
  finalised_checkpoint <- epoch_f <$> read finalized_checkpoint;
  let final_activation_queue = get_validators_eligible_for_activation aq finalised_checkpoint (churn_limit_f state_ctxt);
  next_epoch_activation_queue <- alloc (ActivationQueue.fields []);
  next_epoch_base_reward_cache <- alloc (BaseRewardsCache.fields [] []);
  next_epoch_num_active_validators <- alloc (0 :: u64);
  current_epoch <- get_current_epoch;
  previous_epoch <- get_previous_epoch;
  vs <- read validators;
  _ <- forM (range 0 (unat (var_list_len vs)) 1) (\<lambda>i. do {
     let n = of_nat i;
     validator <- mut (validators !? n);
     balance   <- mut (balances !? n);
     inactivity_score <- mut (inactivity_scores !? n);
     prev_participation <- mut (previous_epoch_participation !? n);
     curr_participation <- mut (current_epoch_participation !? n);
     v <- read validator;
     let is_active_current_epoch = is_active_validator v current_epoch;
     let is_active_previous_epoch = is_active_validator v previous_epoch;
     x <- previous_epoch .+ (Epoch 1);
     let is_eligible = is_active_previous_epoch \<or> (slashed_f v \<and> x < withdrawable_epoch_f v);
     brc <- read base_rewards_cache;
     base_reward <- get_cached_base_reward brc n;
     p_p <- read prev_participation;
     c_p <- read curr_participation;
     let validator_info = ValidatorInfo.fields n (Validator.effective_balance_f v)
                                               base_reward is_eligible (slashed_f v) is_active_current_epoch
                                               is_active_previous_epoch p_p c_p ;
     _ <- when (current_epoch \<noteq> GENESIS_EPOCH) (do {
            is <- read inactivity_score; 
            _  <- (inactivity_score := process_single_inactivity_update is validator_info state_ctxt);
            (balance := process_single_reward_and_penalty balance is validator_info rewards_ctxt state_ctxt)
          });
     ec <- read exit_cache;
     _  <- process_single_registry_update validator validator_info ec final_activation_queue next_epoch_activation_queue state_ctxt;
     v  <- read validator;
     _  <- (balance := process_single_slashing balance v slashings_ctxt progressive_balances);
     _  <- process_single_effective_balance_update balance validator validator_info nepb next_epoch_base_reward_cache effective_balances_ctxt state_ctxt c_p;

     v  <- read validator;
     _  <- when (is_active_validator v (next_epoch_f state_ctxt)) (next_epoch_num_active_validators := next_epoch_num_active_validators .+ 1);
     return ()
   });
  _ <- (progressive_balances_cache := return next_epoch_progressive_balances);
  _ <- (activation_queue := read next_epoch_activation_queue);
  new_base_reward <- compute_base_rewards;
  _ <- (next_epoch_base_reward_cache := return (next_epoch_base_reward_cache\<lparr>base_rewards_f := new_base_reward\<rparr>));
  _ <- (base_rewards_cache := read (next_epoch_base_reward_cache) );
  _ <- (num_active_validators := read next_epoch_num_active_validators);
  return ()
 }"


text \<open>def process_epoch_single_pass(
    state: BeaconState,
) -> None:
    progressive_balances = state.progressive_balances

    state_ctxt = StateContext(
        current_epoch=get_current_epoch(state),
        next_epoch=get_current_epoch(state) + 1,
        is_in_inactivity_leak=is_in_inactivity_leak(state),
        churn_limit=get_validator_churn_limit_fast(state),
    )
    slashings_ctxt = new_slashings_context(state, state_ctxt)
    rewards_ctxt = new_rewards_and_penalties_context(progressive_balances)
    effective_balances_ctxt = new_effective_balances_ctxt()
    next_epoch_progressive_balances = new_next_epoch_progressive_balances(progressive_balances)

    # Determine the final activation queue.
    activation_queue = get_validators_eligible_for_activation(
        state.activation_queue,
        state.finalized_checkpoint.epoch,
        state_ctxt.churn_limit,
    )
    # Create a new speculative activation queue for next epoch.
    next_epoch_activation_queue = ActivationQueue(eligible_validators=[])
    # Create a new base reward cache for next epoch.
    next_epoch_base_reward_cache = BaseRewardCache(effective_balances=[], base_rewards=[])
    # Track the number of active validators for the next epoch.
    next_epoch_num_active_validators = 0

    for (
        index,
        validator,
        balance,
        inactivity_score,
        prev_participation,
        curr_participation,
    ) in zip(
        range(0, len(state.validators)),
        state.validators,
        state.balances,
        state.inactivity_scores,
        state.previous_epoch_participation,
        state.current_epoch_participation,
    ):
        is_active_current_epoch = is_active_validator(validator, current_epoch)
        is_active_previous_epoch = is_active_validator(validator, previous_epoch)
        is_eligible = is_active_previous_epoch or (
            validator.slashed and previous_epoch + 1 < validator.withdrawable_epoch
        )
        validator_info = ValidatorInfo(
            index=index,
            effective_balance=validator.effective_balance,
            base_reward=get_cached_base_reward(base_reward_cache, index),
            is_eligible=is_eligible,
            is_active_current_epoch=is_active_current_epoch,
            is_active_previous_epoch=is_active_previous_epoch,
            previous_epoch_participation=prev_participation,
            current_epoch_participation=curr_participation
        )

        if current_epoch != GENESIS_EPOCH:
            # Note: we may change the presentation of this mutation. Due to primitive types
            # being immutable in Python we cannot pass a mutable reference. Our Isabelle
            # formalisation will likely model the mutation natively (a write to the heap).
            inactivity_score = process_single_inactivity_update(
                inactivity_score,
                validator_info,
                state_ctxt,
            )
            state.inactivity_scores[index] = inactivity_score

            balance = process_single_reward_and_penalty(
                balance,
                inactivity_score,
                validator_info,
                rewards_ctxt,
                state_ctxt
            )
            state.balances[index] = balance

        process_single_registry_update(
            validator,
            validator_info,
            state.exit_cache,
            activation_queue,
            next_epoch_activation_queue,
            state_ctxt,
        )

        balance = process_single_slashing(
            balance,
            validator,
            slashings_ctxt,
            progressive_balances,
        )
        state.balances[index] = balance

        process_single_effective_balance_update(
            balance,
            validator,
            validator_info,
            next_epoch_progressive_balances,
            effective_balances_ctxt,
            state_ctxt,
        )

        # Update num active validators.
        if is_active_next_epoch(validator, next_epoch):
            next_epoch_num_active_validators += 1

    # Update caches for next epoch.
    state.progressive_balances = next_epoch_progressive_balances
    state.activation_queue = next_epoch_activation_queue

    # Compute base reward cache after updating progressive balance cache.
    next_epoch_base_reward_cache.base_rewards = compute_base_rewards(state)
    state.base_reward_cache = next_epoch_base_reward_cache

    state.num_active_validators = next_epoch_num_active_validators\<close>

definition process_epoch_fast :: "(unit, 'a) cont"
  where "process_epoch_fast \<equiv> do {
    _ <- (progressive_balances_cache := new_progressive_balances);
    _ <- (activation_queue := new_activation_queue);
    _ <- (exit_cache := new_exit_cache);
    _ <- (base_rewards_cache := new_base_rewards_cache);
    _ <- process_justification_and_finalization_fast;
    _ <- process_epoch_single_pass;
    _ <- process_eth1_data_reset;
    _ <- process_slashings_reset;
    _ <- process_randao_mixes_reset;
    _ <- process_historical_summaries_update;
    _ <- process_participation_flag_updates;
    _ <- process_sync_committee_updates;
    return ()
}"



text\<open>
Overview for process_epoch_fast

def process_epoch_fast(state: BeaconState) -> None:
    # Pre-conditions (not intended to be executed by implementations).
    assert valid_progressive_balances(state)
    assert valid_activation_queue(state)
    assert valid_exit_cache(state)
    assert valid_base_reward_cache(state)
    assert valid_num_active_validators(state)

    # [CHANGED] Use the aggregate sums to compute justification and finalization.
    process_justification_and_finalization_fast(state)

    # [CHANGED] Compute the majority of processing in a single iteration, utilising the progressive
    # balances for aggregates.
    process_epoch_single_pass(state)

    # [CHANGED] Reorder `process_eth1_data_reset` after `process_effective_balances` which is now
    # part of `process_epoch_single_pass`.
    process_eth1_data_reset(state)

    # [UNCHANGED] These functions are unaffacted.
    process_slashings_reset(state)
    process_randao_mixes_reset(state)
    process_historical_summaries_update(state)
    process_participation_flag_updates(state)
    process_sync_committee_updates(state)
\<close>

end




end