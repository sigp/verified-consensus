theory ProcessEpoch_O
imports Hoare_Logic
begin


record ProgressiveBalancesCache = 
   total_active_balance_f :: u64
   previous_epoch_flag_attesting_balances_f :: "u64 list"
   current_epoch_flag_attesting_balances_f ::  "u64 list"

find_consts ProgressiveBalancesCache

record ActivationQueue =
   eligible_validators_f :: "(Epoch \<times> u64) list"

locale extended_vc = verified_con  +
  fixes "progressive_balances_cache" :: 'b 

begin

term "[x \<mapsto> y]"

definition "maps_to x y \<equiv> \<lambda>s. s = [x \<mapsto> y]"

term "(maps_to addr (list [ptr total_active_balance,
                           ptr previous_epoch_flag_attesting_balances,
                           ptr current_epoch_flag_attesting_balances]) \<and>*  maps_to total_active_balance (u64 (total_active_balance_f cache)))"

definition "translate_ProgressiveBalancesCache" :: 
    "'b \<Rightarrow> ProgressiveBalancesCache \<Rightarrow> (('b \<Rightarrow> 'b heap_value option) \<Rightarrow> bool)"
where "translate_ProgressiveBalancesCache addr cache s \<equiv> 
        \<exists>total_active_balance previous_epoch_flag_attesting_balances
         current_epoch_flag_attesting_balances.
         (maps_to addr (list [ptr total_active_balance,
                           ptr previous_epoch_flag_attesting_balances,
                           ptr current_epoch_flag_attesting_balances]) \<and>*
          maps_to total_active_balance (u64 (total_active_balance_f cache)) \<and>* 
          maps_to previous_epoch_flag_attesting_balances ((list o map u64 o previous_epoch_flag_attesting_balances_f) cache) \<and>*
          maps_to current_epoch_flag_attesting_balances ((list o map u64 o current_epoch_flag_attesting_balances_f) cache)) s"

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


definition "process_justification_and_finalization_fast" ::  "(unit, 'a) cont"
  where "process_justification_and_finalization_fast \<equiv> do {
     previous_epoch <- get_previous_epoch;
     current_epoch <- get_current_epoch;
     epoch1 \<leftarrow> GENESIS_EPOCH .+ Epoch 1;
    if current_epoch \<le> epoch1 then
      return ()
    else do {
      pbc \<leftarrow> read_ProgressiveBalancesCache progressive_balances_cache;
      let (total_active_balance) = total_active_balance_f pbc;
      let (previous_epoch_flag_attesting_balances) = previous_epoch_flag_attesting_balances_f pbc;
      let (previous_target_balance) = previous_epoch_flag_attesting_balances ! (of_nat TIMELY_TARGET_FLAG_INDEX);
      let (current_epoch_flag_attesting_balances) = current_epoch_flag_attesting_balances_f pbc;
      let (current_target_balance) =  current_epoch_flag_attesting_balances ! (of_nat TIMELY_TARGET_FLAG_INDEX) ;
      _ \<leftarrow> weigh_justification_and_finalization
         total_active_balance previous_target_balance current_target_balance;
      return ()
      
}}"
end

end