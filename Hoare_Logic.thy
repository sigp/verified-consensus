theory Hoare_Logic
  imports ProcessEpoch "algebra/rg-algebra/AbstractAtomicTest/Programming_Constructs" 
  "jormungand/sep_algebra/Sep_Tactics"
  Word_Lib.More_Divides Word_Lib.Word_EqI
Word_Lib.Word_64 Word_Lib.Bitwise Word_Lib.Word_Lemmas
begin

declare [[show_sorts=false]]


lemma map_insort_sorted: "mono f \<Longrightarrow> sorted xs \<Longrightarrow> map f (insort a xs) = insort (f a) (map f xs)" 
  apply (induct xs; clarsimp)
  apply (safe)
  using monoD apply blast
  using monoD apply blast
   apply (simp add: monoD order_antisym)
  by (smt (verit) insort_is_Cons insort_key.simps(2)
      linorder_le_cases list.set_cases list.set_intros(1) list.simps(9) monotoneD order_antisym)


lemma Id_on_relcomp_eq: "Id_on P O Id_on Q = Id_on (P \<inter> Q)" 
  by (safe; clarsimp simp: Id_on_def, rule relcompI, blast, blast)


instantiation option :: (type) stronger_sep_algebra begin

fun sep_disj_option :: "'b option \<Rightarrow> 'b option \<Rightarrow> bool" where
 "sep_disj_option (Some x) (Some y) = False" | 
 "sep_disj_option x y = True" 

fun plus_option where
 "plus_option (Some x) (Some y) = Some x" | 
 "plus_option (None) y = y" |
 "plus_option  x (None) = x"

lemma [simp]: "x + None = x"
  by (case_tac x; clarsimp)

definition "zero_option = None"

instance
  apply (standard, case_tac x; (clarsimp simp: zero_option_def)?)
     apply (case_tac x; case_tac y; clarsimp)
      apply (case_tac x; case_tac y; clarsimp)
      apply (case_tac x; case_tac y; clarsimp)
   apply (case_tac x; case_tac y; case_tac z; clarsimp)
  done
end

instantiation "fun" :: (type, stronger_sep_algebra) stronger_sep_algebra begin

definition sep_disj_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
 "sep_disj_fun f g \<equiv> (\<forall>x. f x ## g x)" 

definition plus_fun where
 "plus_fun f g = (\<lambda>x. f x + g x)"

lemma [simp]: "x + None = x"
  by (case_tac x; clarsimp)

definition "zero_fun = (\<lambda>x. 0)"

instance
  apply (standard; (rule ext)?, (clarsimp simp: plus_fun_def sep_disj_fun_def zero_fun_def)? )
     apply (metis sep_disj_commute)
  apply (metis sep_add_commute)
   apply (metis sep_add_assoc)
  apply (blast)
  done
end

instantiation prod :: (stronger_sep_algebra, stronger_sep_algebra) stronger_sep_algebra begin

fun sep_disj_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
 "sep_disj_prod (a,b) (x,y) \<longleftrightarrow> (a ## x \<and> b ## y)" 

fun plus_prod where
 "plus_prod (a,b) (x,y) = (a + x, b + y)" 


definition "zero_prod = (0,0)"

instance
  apply (standard, case_tac x; (clarsimp simp: zero_prod_def split: prod.splits)?)
     apply (metis sep_disj_commute)
  apply (metis sep_add_commute)
   apply (metis sep_add_assoc)
  by blast

end

instantiation unit ::  stronger_sep_algebra begin

fun sep_disj_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where
 "sep_disj_unit x y \<longleftrightarrow> True" 

fun plus_unit :: "unit \<Rightarrow> unit \<Rightarrow> unit" where
 "plus_unit x y = ()" 


definition "zero_unit = ()"

instance
  by (standard, case_tac x; (clarsimp simp: zero_unit_def)?)
 

end





instantiation BeaconState_ext :: (stronger_sep_algebra) stronger_sep_algebra begin


definition sep_disj_BeaconState_ext :: "'a BeaconState_scheme \<Rightarrow> 'a BeaconState_scheme \<Rightarrow> bool" 
  where "sep_disj_BeaconState_ext x y == 
  genesis_time_f x ## genesis_time_f y \<and> 
  genesis_validators_root_f x ## genesis_validators_root_f y \<and> 
  slot_f x ## slot_f y \<and> fork_f x ## fork_f y \<and> 
  latest_block_header_f x ## latest_block_header_f y \<and> 
  block_roots_f x ##  block_roots_f y \<and>
  state_roots_f x ##  state_roots_f y \<and> 
  historical_roots_f x ## historical_roots_f y \<and>
  eth1_data_f x ## eth1_data_f y \<and>
  eth1_data_votes_f x ## eth1_data_votes_f y \<and>
  eth1_deposit_index_f x ## eth1_deposit_index_f y \<and>
  validators_f x ## validators_f y \<and>
  balances_f x ## balances_f y \<and>
  randao_mixes_f x ## randao_mixes_f y \<and>
  slashings_f x ## slashings_f y \<and>
  previous_epoch_participation_f x ## previous_epoch_participation_f y \<and>
  current_epoch_participation_f x ## current_epoch_participation_f y \<and>
  justification_bits_f x ## justification_bits_f y \<and>
  previous_justified_checkpoint_f x ## previous_justified_checkpoint_f y \<and>
  current_justified_checkpoint_f x ## current_justified_checkpoint_f y \<and>
  finalized_checkpoint_f x ## finalized_checkpoint_f y \<and>
  inactivity_scores_f x ## inactivity_scores_f y \<and>
  current_sync_committee_f x ## current_sync_committee_f y \<and>
  next_sync_committee_f x ## next_sync_committee_f y \<and> 
  latest_execution_payload_header x ## latest_execution_payload_header y \<and> 
  next_withdrawal_index_f x ## next_withdrawal_index_f y \<and> 
  next_withdrawal_validator_index_f x ## next_withdrawal_validator_index_f y \<and>
  historical_summaries_f x ## historical_summaries_f y \<and> BeaconState.more x ## BeaconState.more y"

definition plus_BeaconState_ext :: "'a BeaconState_scheme \<Rightarrow> 'a BeaconState_scheme \<Rightarrow> 'a BeaconState_scheme" 
  where "plus_BeaconState_ext x y == 
  \<lparr> genesis_time_f = genesis_time_f x + genesis_time_f y,
  genesis_validators_root_f = genesis_validators_root_f x + genesis_validators_root_f y, 
  slot_f = slot_f x + slot_f y, fork_f = fork_f x + fork_f y ,
  latest_block_header_f = latest_block_header_f x + latest_block_header_f y ,
  block_roots_f = block_roots_f x + block_roots_f y,
  state_roots_f = state_roots_f x + state_roots_f y ,
  historical_roots_f = historical_roots_f x + historical_roots_f y,
  eth1_data_f = eth1_data_f x + eth1_data_f y,
  eth1_data_votes_f = eth1_data_votes_f x + eth1_data_votes_f y,
  eth1_deposit_index_f = eth1_deposit_index_f x + eth1_deposit_index_f y,
  validators_f = validators_f x + validators_f y,
  balances_f = balances_f x + balances_f y,
  randao_mixes_f = randao_mixes_f x + randao_mixes_f y,
  slashings_f = slashings_f x + slashings_f y,
  previous_epoch_participation_f = previous_epoch_participation_f x + previous_epoch_participation_f y,
  current_epoch_participation_f = current_epoch_participation_f x + current_epoch_participation_f y,
  justification_bits_f = justification_bits_f x + justification_bits_f y,
  previous_justified_checkpoint_f = previous_justified_checkpoint_f x + previous_justified_checkpoint_f y,
  current_justified_checkpoint_f = current_justified_checkpoint_f x + current_justified_checkpoint_f y,
  finalized_checkpoint_f = finalized_checkpoint_f x + finalized_checkpoint_f y,
  inactivity_scores_f = inactivity_scores_f x + inactivity_scores_f y,
  current_sync_committee_f = current_sync_committee_f x + current_sync_committee_f y,
  next_sync_committee_f = next_sync_committee_f x + next_sync_committee_f y,
  latest_execution_payload_header = latest_execution_payload_header x + latest_execution_payload_header y,
  next_withdrawal_index_f = next_withdrawal_index_f x + next_withdrawal_index_f y, 
  next_withdrawal_validator_index_f = next_withdrawal_validator_index_f x + next_withdrawal_validator_index_f y,
  historical_summaries_f = historical_summaries_f x + historical_summaries_f y, 
  \<dots> = BeaconState.more x + BeaconState.more y \<rparr>"

definition "zero_BeaconState_ext \<equiv> \<lparr> genesis_time_f = None,
  genesis_validators_root_f = None, 
  slot_f = None, fork_f = None ,
  latest_block_header_f = None ,
  block_roots_f = None,
  state_roots_f = None ,
  historical_roots_f = None,
  eth1_data_f = None,
  eth1_data_votes_f = None,
  eth1_deposit_index_f = None,
  validators_f = None,
  balances_f = None,
  randao_mixes_f = None,
  slashings_f = None,
  previous_epoch_participation_f = None,
  current_epoch_participation_f = None,
  justification_bits_f = None,
  previous_justified_checkpoint_f = None,
  current_justified_checkpoint_f = None,
  finalized_checkpoint_f = None,
  inactivity_scores_f = None,
  current_sync_committee_f = None,
  next_sync_committee_f = None,
  latest_execution_payload_header = None,
  next_withdrawal_index_f = None, 
  next_withdrawal_validator_index_f = None,
  historical_summaries_f = None, \<dots> = 0\<rparr>"

instance

  apply (standard; (clarsimp simp: plus_BeaconState_ext_def sep_disj_BeaconState_ext_def zero_BeaconState_ext_def)?)
     apply (clarsimp simp: sep_disj_commute)
    apply (metis sep_add_commute)
   apply (intro conjI; metis sep_add_assoc)
  apply (safe; clarsimp)
  done
end





locale hoare_logic = verified_con + strong_spec begin


definition "hoare_triple P f Q \<equiv>   run f \<le> assert (Collect P); spec (UNIV \<triangleright> (Collect Q)) "


notation hoare_triple ("\<lblot>_\<rblot> _ \<lblot>_\<rblot>")


lemma setState_spec: "(run (setState s)) \<le> spec (UNIV \<triangleright> {s}) "
  apply (clarsimp simp: spec_def)
  apply (rule conj_refine)
   apply (clarsimp simp: run_def setState_def)
  using  pspec_ref_pgm apply presburger
    apply (clarsimp simp: run_def setState_def)
  by (meson order_trans spec_ref_pgm spec_term)


lemma set_state_valid: "hoare_triple \<top> (setState s) (eq s)"
  apply (clarsimp simp: hoare_triple_def assert_top)
  by (metis assert_top seq_nil_left setState_spec top_set_def)


lemma getState_spec: "(run (getState)) \<le> spec (UNIV) "
  apply (clarsimp simp: spec_def)
  apply (rule conj_refine)
   apply (clarsimp simp: run_def getState_def)
  apply (simp add: Nondet_test_nil chaos_ref_nil pspec_univ)
  apply (clarsimp simp: run_def getState_def)
  by (simp add: Nondet_test_nil term_nil)

lemma getState_valid: "hoare_triple \<top> (getState) \<top>"
  apply (clarsimp simp: hoare_triple_def assert_top)
  apply (simp add: getState_spec spec_test_restricts test_top)
  by (metis UNIV_eq_I assert_top getState_spec mem_Collect_eq
            seq_nil_left seq_nil_right test_top top1I)


definition "bind_rel P Q = (Id_on P) O Q "


lemma pgm_post_assert: "\<pi> (UNIV \<triangleright> S) = \<pi> (UNIV \<triangleright> S) ; assert S"
  by (metis pgm_test_post seq_assoc test_seq_assert)

lemma rewrite: "UNIV \<triangleright> (Q `` (P \<inter> {s})) = (UNIV \<triangleright> {s}) O (P \<triangleleft> Q)  "
  apply (safe; clarsimp simp: Image_iff restrict_range_def restrict_domain_def)
  by blast


lemma stutter_range_restriction: "a \<in> P \<Longrightarrow> (a,a) \<in> range_restriction P"
  apply (clarsimp)
  done


lemma restrict_domain_compose_Id: "(P \<triangleleft> Q) = ((Id_on P) O Q)" 
  apply (rule set_eqI)
  apply (safe)
   apply (clarsimp simp: restrict_range_def  restrict_domain_def, rule relcompI)
    apply (erule Id_onI, assumption)
  by (clarsimp simp: restrict_range_def  restrict_domain_def)


 


lemma test_smaller_assert: "p \<subseteq> q \<Longrightarrow> test p ; assert q = test p"
  apply (clarsimp simp: assert_def)
  apply (subst par.seq_nondet_distrib)
  by (metis assert_bot le_iff_inf seq_assoc sup_bot.right_neutral test.hom_bot test_seq_assert test_seq_compl test_seq_magic test_seq_test)




lemma hoare_chain: "(\<lbrace>P\<rbrace>;\<lparr>Q\<rparr>; \<lbrace>P'\<rbrace>;\<lparr>Q'\<rparr>) \<le> \<lbrace>P - (converse Q `` (-P'))\<rbrace>;\<lparr>(Q) O Q'\<rparr>" 
  apply (subst assert_restricts_spec) back
  apply (subst assert_galois_test)
  apply (subst domain_restrict_relcomp[symmetric])
  apply (rule order_trans[rotated], rule spec_seq_introduce[where p="P'"])
  apply (rule_tac y="(\<tau> (P - Q\<inverse> `` (- P')) ; \<lbrace>P\<rbrace> ; \<lparr>Q\<rparr>) ; (\<lbrace>P'\<rbrace> ; \<lparr>Q'\<rparr>)" in order_trans)
   apply (clarsimp simp: seq_assoc)
  apply (subst seq_assoc, rule seq_mono[rotated], rule order_refl)
  apply ( subst test_smaller_assert)
   apply (blast)
  apply (subst test_seq_refine)
  apply (subst test_restricts_spec)
  apply (rule seq_mono, rule order_refl)
  apply (rule spec_strengthen)
  apply (clarsimp simp: restrict_domain_def restrict_range_def Image_iff)
  apply (blast)
  done


lemma set_state_hoare_inner: "\<pi> (UNIV \<triangleright> {s}) \<le> \<lbrace>UNIV\<rbrace> ; spec (UNIV \<triangleright> {s})"
  by (simp add: assert_top spec_ref_pgm)

lemma univ_sub_neg: "UNIV - P = - P"
  apply (safe; clarsimp)
  done


lemma setState_seq': "run (g ()) \<le> spec P \<Longrightarrow>  (run (do {x <- setState s ; g x})) \<le> spec (UNIV \<triangleright> {s} O P) "
  apply (clarsimp simp: run_def bindCont_def setState_def)
  apply (rule order_trans[rotated], rule spec_to_sequential)
  apply (rule seq_mono)
   apply (rule spec_ref_pgm)
  apply (assumption)
  done


lemma spec_ref_pspec: "spec P \<le> pspec P "
  apply (clarsimp simp: spec_def)
  by (simp add: conj_conjoin_non_aborting term_nonaborting)

lemma specI: "x \<le> term \<Longrightarrow> x \<le> pspec P \<Longrightarrow> x \<le> spec P"
  apply (clarsimp simp: spec_def)
  apply (rule conj_refine, assumption+)
  done

lemma pspec_strengthen: "p \<subseteq> q \<Longrightarrow> pspec p \<le> pspec q" by (erule pspec_strengthen)

lemma spec_strengthen: "p \<subseteq> q \<Longrightarrow> spec p \<le> spec q" by (erule spec_strengthen)


lemma restrict_dom_singleton: "restrict_domain {x} {x. P x} = {(a,b). a = x \<and> P (a, b) }"
  apply (clarsimp simp: restrict_domain_def)
  apply (safe)
  done

lemma assert_commute: "assert a ; assert b = assert b ; assert a"
  by (simp add: Int_commute assert_seq_assert)

lemma test_spec: "test {t} \<le> \<lbrace>UNIV\<rbrace> ; \<lparr>Id_on {t}\<rparr>"
  apply (clarsimp simp: assert_top)
  apply (rule spec_refine)
  using dual_order.trans nil_ref_test term_nil apply blast
  apply (clarsimp)
  using test_inf_eq_seq test_seq_commute test_seq_refine by fastforce


named_theorems wp

lemma getState_seq: "(\<And>x. run (g x) \<le> spec (P x)) \<Longrightarrow>  (run (do { x <- getState ; g (x)})) \<le> spec ({(s, s'). (s, s') \<in> P s}) "
  apply (clarsimp simp: run_def bindCont_def getState_def)
  apply (rule specI)
  apply (subst Sup_le_iff, clarsimp)
   apply (atomize)
   apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)
  using nil_ref_test order_trans seq_mono spec_def spec_term apply fastforce
  apply (subst Sup_le_iff, clarsimp)
   apply (atomize)
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)
  apply (drule order_trans, rule spec_ref_pspec)
  apply (rule order_trans, rule seq_mono, rule order_refl, assumption)
  apply (subst test_seq_refine)
  apply (subst test_restricts_pspec)
  apply (subst test_restricts_pspec) back

  apply (rule seq_mono, rule order_refl)
  apply (rule pspec_strengthen)
  apply (subst restrict_dom_singleton)
  apply (clarsimp simp: restrict_domain_def)
  done


lemma test_refines_id_spec: "\<tau> S \<le> spec (Id_on S) "
  apply (rule spec_refine; clarsimp?)
  using dual_order.trans nil_ref_test term_nil apply blast
  using test_inf_eq_seq test_seq_commute test_seq_refine by auto

lemma test_inf_singletons: "(\<tau> {x} \<sqinter> \<tau> {xa}) = (if x = xa then test {x} else \<bottom>)"
  by (metis Int_empty_right Int_insert_right_if0 insert_inter_insert singletonD test.hom_bot test.hom_inf)


lemma test_prefix_spec: "\<tau> {x} ; spec P \<le> spec {(a, b). a = x \<and> (a, b) \<in> P}" 
  apply (subst test_seq_refine)
   apply (subst test_restricts_spec)  
   apply (subst test_restricts_spec) 
   apply (rule seq_mono; clarsimp?)
   apply (rule spec_strengthen)
   apply (clarsimp simp: restrict_range_def restrict_domain_def restrict_dom_singleton Sup_le_iff)
  done


lemma spec_singletonI[intro!]: "x \<in> S \<Longrightarrow> \<lparr>{x}\<rparr> \<le> \<lparr>S\<rparr>"
  by (simp add: spec_strengthen)



lemma hoare_anti_mono: "hoare_triple P' f Q' \<Longrightarrow> P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> hoare_triple P f Q"
  apply (clarsimp simp: hoare_triple_def)
  apply (rule order_trans)
   apply (assumption)
  apply (rule seq_mono)
  using assert_iso apply blast
  apply (rule spec_strengthen)
  by (safe; clarsimp simp: restrict_range_def le_fun_def)


lemma restrict_range_UNIV[simp]: "UNIV \<triangleright> S = UNIV \<times> S "
  by (safe; clarsimp simp: restrict_range_def) 


lemma restrict_domain_UNIV[simp]: "UNIV \<triangleleft> R = R "
  by (safe; clarsimp simp: restrict_domain_def) 




lemmas bind_assoc =  kcomp_assoc[simplified k_comp_def]

lemma bindCont_assoc: "bindCont f (\<lambda>a. bindCont (g a) h) = bindCont (bindCont f g) h"
  by (clarsimp simp: bindCont_def)


lemma if_seq: 
  "run (bindCont P c) \<le> assert S ; spec R \<Longrightarrow> run (bindCont Q c) \<le> assert S' ; spec R' \<Longrightarrow>
   run (do {x <- (if B then P else Q); c x}) \<le> assert (if B then S else S') ; spec (if B then R else R')"
  apply (clarsimp split: if_splits)
  done

lemma if_seq_valid: 
  "hoare_triple  S (bindCont P c) R \<Longrightarrow> hoare_triple S' (bindCont Q c) R' \<Longrightarrow>
   hoare_triple (if B then S else S') (do {x <- (if B then P else Q); c x}) (if B then R else R')"
  apply (clarsimp split: if_splits)
  done


lemmas if_seq_valid' = if_seq_valid[where c=return, simplified bindCont_return]



lemma run_fail_assert: "run (bindCont fail c) \<le> assert {} ; \<lparr>{}\<rparr>"
  apply (clarsimp simp: run_def fail_def bindCont_def spec_def pspec_def assert_def)
  using assert_bot local.assert_def by force

lemma Collect_bot[simp]:"Collect \<bottom> = {}"
  apply (clarsimp)
  done

lemma run_fail_assert_valid: "hoare_triple \<bottom> (bindCont fail c) R"
  apply (clarsimp simp: run_def fail_def bindCont_def spec_def pspec_def assert_def hoare_triple_def)
  using assert_bot local.assert_def by force

declare in_dom_iff[simp]

lemma "x \<in> S \<triangleleft> R \<longleftrightarrow> fst x \<in> S \<and> x \<in> R"
  by (clarsimp simp: restrict_domain_def, safe; clarsimp)

definition "wf_lens l \<longleftrightarrow> (\<forall>s v. get l (set l s v) = v)"

definition "maps_to l v s \<equiv> wf_lens l \<and> get l (fst s) = Some v" 

lemma restrict_UNIV_times: "P \<triangleleft> (UNIV \<times> R) = (P \<times> R)"
  by (safe; clarsimp)

lemma spec_ref_pgm':"R \<subseteq> R' \<Longrightarrow> pgm R \<le> spec R'"
  by (meson dual_order.trans pgm.hom_mono spec_ref_pgm)

lemma write_beacon_sep: "hoare_triple ( (maps_to l v \<and>* R)) (write_beacon l v') ( (maps_to l v' \<and>* R))"
  apply (clarsimp simp: hoare_triple_def run_def write_beacon_def bindCont_def getState_def Sup_le_iff)
  apply (intro conjI impI)
   apply (clarsimp simp: assert_galois_test)
   apply (clarsimp simp: seq_assoc[symmetric] test_seq_test)
   apply (clarsimp simp: fail_def)
   apply (subgoal_tac "\<tau> (Collect (maps_to l v \<and>* R)) \<sqinter> \<tau> {(a, b)} = \<bottom>"; clarsimp?)
   defer
   apply (clarsimp)
   apply (clarsimp simp: assert_galois_test seq_assoc[symmetric] test_seq_test setState_def pgm_test_pre domain_restrict_twice )
   apply (clarsimp simp: restrict_UNIV_times)
   apply (rule spec_ref_pgm')
   apply (clarsimp)
  sorry




abbreviation (input) "member S \<equiv> (\<lambda>x. x \<in> S)"

lemma run_read_beacon_split[simp]: "run (bindCont (read l) c) = ((run (read l)) ; (\<Squnion>x. \<tau> {s. get l (fst s) = Some x}  ; run (c x)))"
  apply (clarsimp simp: run_def bindCont_def read_beacon_def getState_def return_def Nondet_seq_distrib split: if_splits )
  apply (rule antisym; (clarsimp simp: Sup_le_iff Nondet_seq_distrib)?)
   apply (safe; (clarsimp split: if_splits)?)
    apply (rule Sup_upper)

     apply (clarsimp simp: image_iff)
     apply (rule_tac x=a in exI)
    apply (rule_tac x=b in exI)
    apply (safe; clarsimp?)
    apply (clarsimp simp: fail_def seq_assoc)
   apply (clarsimp simp: return_def)
   apply (rule Sup_upper2)

     apply (clarsimp simp: image_iff)
     apply (rule_tac x=a in exI)
    apply (rule_tac x=b in exI)
    apply (safe; clarsimp?)
  apply (rule refl)
   apply (clarsimp simp: return_def par.seq_Nondet_distrib)
   apply (rule Sup_upper2, clarsimp simp: image_iff)
  apply (rule_tac x=y in exI, rule refl)
  using seq_mono_left test.hom_mono test_seq_refine apply force
  apply (safe)
   apply (clarsimp simp: fail_def)
 apply (rule Sup_upper2)

     apply (clarsimp simp: image_iff)
     apply (rule_tac x=a in exI)
    apply (rule_tac x=b in exI)
    apply (clarsimp, rule refl, clarsimp simp: fail_def seq_assoc)
  apply (clarsimp simp: return_def)
  apply (clarsimp simp: par.seq_Nondet_distrib Sup_le_iff)
  apply (case_tac "y = aa"; clarsimp?)
  apply (rule Sup_upper2, clarsimp simp: image_iff)

     apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
   apply (clarsimp simp: return_def)
   apply (rule refl)
   apply (meson dual_order.refl seq_mono_right test_seq_refine)
  apply (subst seq_assoc[symmetric], subst test_seq_test)
  apply (clarsimp)
  done



lemma run_write_beacon_split[simp]: "run (bindCont (write_beacon l v') c) = ((run (write_beacon l v')) ; run (c ()))"
  apply (clarsimp simp: run_def bindCont_def write_beacon_def getState_def)
  apply (rule antisym; (clarsimp simp: Sup_le_iff Nondet_seq_distrib)?)
   apply (safe)
     apply (rule Sup_upper)
     apply (clarsimp simp: image_iff)
     apply (rule_tac x=a in exI)
     apply (rule_tac x=b in exI)
     apply (safe; clarsimp simp: fail_def)
     apply (simp add: seq_assoc)
    apply (rule Sup_upper)
 apply (clarsimp simp: image_iff)
     apply (rule_tac x=a in exI)
     apply (rule_tac x=b in exI)
     apply (safe; clarsimp simp: fail_def)
    apply (simp add: seq_assoc)
    apply (clarsimp simp: setState_def)
  apply (rule Sup_upper)
 apply (clarsimp simp: image_iff)
     apply (rule_tac x=a in exI)
     apply (rule_tac x=b in exI)
     apply (safe; clarsimp simp: fail_def)
   apply (simp add: seq_assoc)
  apply (rule Sup_upper)
 apply (clarsimp simp: image_iff)
     apply (rule_tac x=a in exI)
     apply (rule_tac x=b in exI)
     apply (safe; clarsimp simp: fail_def)
  apply (simp add: seq_assoc)
  apply (clarsimp simp: setState_def)
  done

lemma hoare_chain': "Q \<subseteq> P' \<Longrightarrow>
    (assert P ; spec (UNIV \<times> Q)) ; (assert P' ; spec (UNIV \<times> Q')) \<le> assert P ; spec (UNIV \<times> Q')"
  apply (subst assert_restricts_spec) back back
  apply (simp only: restrict_UNIV_times)
  apply (clarsimp simp: seq_assoc[symmetric])
  apply (rule order_trans)
   apply (rule hoare_chain)
  apply (subst assert_restricts_spec)
  apply (rule seq_mono)
   apply (clarsimp simp: assert_iso[symmetric])
   apply (blast)
  apply (rule spec_strengthen)
  apply (clarsimp)
  done



lemma write_beacon_wp[wp]: "hoare_triple ( P) (c ()) Q \<Longrightarrow> hoare_triple ( (maps_to l v \<and>* (maps_to l v' \<longrightarrow>* P))) (do {x <- write_beacon l v' ; c x}) ( Q)"
  apply (clarsimp simp: hoare_triple_def)
  apply (rule order_trans)
   apply (rule seq_mono)
    apply (rule write_beacon_sep[simplified hoare_triple_def, where R="(maps_to l v' \<longrightarrow>* P)"], assumption)
  apply (clarsimp simp: restrict_range_UNIV)
  apply (rule hoare_chain', clarsimp)
  apply (sep_solve)
  done




lemma read_sep: " hoare_triple ( (maps_to l v \<and>* R)) (read l) ( (maps_to l v \<and>* R))"
  apply (clarsimp simp: hoare_triple_def run_def read_beacon_def bindCont_def getState_def Sup_le_iff, safe)
   apply (clarsimp simp: fail_def assert_galois_test)
   defer
   apply (clarsimp simp: return_def)
   apply (metis assert_galois_test nil_ref_test restrict_range_UNIV seq_mono 
   seq_mono_left seq_nil_left spec_test_restricts spec_univ term_nil test_seq_commute)
  apply (subgoal_tac "\<tau> (Collect (maps_to l v \<and>* R)) ; \<tau> {(a, b)} \<le> \<bottom>")
  apply (metis bot.extremum inf.absorb_iff2 inf_bot_left seq_assoc seq_magic_left)
  sorry

lemma times_restrict_range[simp]: "(UNIV \<times> P) \<triangleright> Q = (UNIV \<times> (P \<inter> Q))"
  by (safe; (clarsimp simp: restrict_range_def)?)

lemma maps_to_get_wf:"(maps_to l v \<and>* R) (a, b) \<Longrightarrow> get l a = Some v"
  apply (clarsimp simp: sep_conj_def maps_to_def)
  sorry

lemma read_beacon_wp[wp]: "(\<And>a. hoare_triple ( P a) (c a) (Q )) \<Longrightarrow> hoare_triple ( (maps_to l v \<and>* (maps_to l v \<longrightarrow>*  (P v )))) (do {v <- read_beacon l ; c v}) (Q  )"
  apply (clarsimp simp: hoare_triple_def bindCont_def run_def read_beacon_def getState_def )
  apply (clarsimp simp: Sup_le_iff)
  apply (safe)
   apply (clarsimp simp: fail_def assert_galois_test)
   defer
   apply (clarsimp simp: fail_def assert_galois_test return_def)
   apply (case_tac "y = v"; clarsimp?)
    apply (subst seq_assoc[symmetric])
    apply (subst test_seq_test)
    apply (rule order_trans, rule seq_mono_left)
     apply (rule test.hom_mono[where p="Collect (P v)"])
     apply (clarsimp)
     apply (sep_solve)
    apply (blast)
  apply (subst seq_assoc[symmetric])
   apply (subst test_seq_test)
 apply (rule order_trans, rule seq_mono_left)
    apply (rule test.hom_mono[where p="{}"])
    apply (clarsimp)
    defer
    apply (clarsimp)
  apply (subst seq_assoc[symmetric])
   apply (subst test_seq_test)
 apply (rule order_trans, rule seq_mono_left)
    apply (rule test.hom_mono[where p="{}"])
    apply (clarsimp)
    defer
    apply (clarsimp)
   apply (drule maps_to_get_wf, clarsimp)
  apply (drule maps_to_get_wf, clarsimp)
  done
 

definition "swap l l' \<equiv> do {x <- read_beacon l;
                            y <- read l';
                            _ <- write_beacon l' x;
                            write_beacon l  y}"


definition "add_fields l l' \<equiv> do {x <- read_beacon l;
                                  y <- read_beacon l';
                                  return (x + y)}"


definition "set_max a b c \<equiv> do { x <- read_beacon a;
                                  y <- read_beacon b;
                                  (if (x \<le> y) then write_beacon c y else write_beacon c x)}"


lemma return_wp: "hoare_triple P (return c) P"
  apply (clarsimp simp: hoare_triple_def)
  apply (clarsimp simp: run_def return_def)
  by (metis assert_galois_test restrict_range_UNIV seq_mono_left seq_nil_left seq_nil_right spec_test_restricts spec_univ term_nil)




lemma hoare_strengthen_post: "hoare_triple P f Q' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> hoare_triple P f Q"
  apply (clarsimp simp: hoare_triple_def le_fun_def)
  apply (rule order_trans)
   apply (assumption)
  apply (rule seq_mono)
  using assert_iso apply blast
  apply (rule spec_strengthen)
  by (fastforce)

lemma hoare_weaken_pre: "hoare_triple P' f Q \<Longrightarrow> P \<le> P' \<Longrightarrow> hoare_triple P f Q"
  apply (clarsimp simp: hoare_triple_def)
  apply (rule order_trans)
   apply (assumption)
  apply (rule seq_mono)
  using assert_iso apply blast
  by (clarsimp)

lemma swap_sep: "hoare_triple ( (maps_to l v \<and>* maps_to l' v' \<and>* R)) (swap l l') ( (maps_to l v' \<and>* maps_to l' v \<and>* R) )"
  apply (clarsimp simp: swap_def)
  apply (rule hoare_weaken_pre)
   apply (rule read_beacon_wp)
  apply (rule read_beacon_wp[where v=v'])
   apply (rule wp )+
  apply (rule  wp[where c=return, simplified bindCont_return, OF return_wp])
  apply (clarsimp)
   apply (sep_solve)
  done

lemma swap_wp: "hoare_triple ( P) (c ()) Q  \<Longrightarrow> hoare_triple ( (maps_to l v \<and>* maps_to l' v' \<and>* (maps_to l v' \<and>* maps_to l' v \<longrightarrow>* P))) (do {x <- swap l l'; c x}) (Q)"
  apply (clarsimp simp: swap_def)
  apply (rule hoare_anti_mono)
    apply (clarsimp simp: bindCont_assoc[symmetric])
   apply (rule wp )+
  apply (assumption)
  apply (clarsimp)
  apply (sep_cancel)+
   apply (sep_solve)
  apply (clarsimp)
  done


lemma return_triple: "hoare_triple P (bindCont C return) Q \<Longrightarrow> hoare_triple P C Q "
  apply (clarsimp simp: bindCont_return)
  done


method wp = ((simp only: bindCont_assoc[symmetric] bindCont_return')?,
       (rule wp return_wp wp[THEN return_triple]) | assumption )+ 


lemma add_fields_wp: "(\<And>a. hoare_triple ( (P a)) (c a) (Q))  \<Longrightarrow>
    hoare_triple ( (maps_to l v \<and>* maps_to l' v' \<and>* (maps_to l v \<and>* maps_to l' v' \<longrightarrow>* P (v + v'))))
         (do {x <- add_fields l l'; c x}) (Q )"
  apply (clarsimp simp: add_fields_def)
  apply (rule hoare_weaken_pre)
    apply (wp)
  by (clarsimp, sep_cancel+, sep_solve)


thm swap_wp[where c=return, simplified bindCont_return]

thm add_fields_wp[where c=return, simplified bindCont_return]

find_theorems "if _ then _ else _" bindCont


 


lemma if_wp[wp]: 
  "(B \<Longrightarrow> hoare_triple  ( S) ( bindCont P c) R) \<Longrightarrow> (\<not>B \<Longrightarrow> hoare_triple ( S') (bindCont Q c) R) \<Longrightarrow>
   hoare_triple ( (if B then S else S'))  (do {x <- (if B then P else Q); c x}) R"
  apply (clarsimp split: if_splits)
  done

lemma inf_spec: " \<Inter> (range P) \<le> P (a, b)"
  apply (clarsimp)
  done

lemma getState_wp[wp]: "(\<And>a. hoare_triple (P a) (c a) Q) \<Longrightarrow> 
  hoare_triple (\<lambda>x. P x x) (bindCont getState c) Q"
  apply (clarsimp simp: getState_def hoare_triple_def bindCont_def run_def Sup_le_iff assert_galois_test test_restricts_Nondet)
  apply (atomize)
  apply (erule_tac x=a in allE)
  apply (erule_tac x=b in allE)
  apply (erule order_trans[rotated])
  using seq_mono_left test.hom_mono by force


lemma run_setState_distrib: "run (bindCont (setState s) c) = run (setState s); run (c ())"
  by (clarsimp simp: run_def bindCont_def setState_def)

lemma run_setState_le: "run (setState s) \<le> assert UNIV ; spec (UNIV \<times> {s})"
  apply (clarsimp simp: setState_def run_def)
  by (simp add: assert_top spec_ref_pgm)

lemma setState_wp[wp]: " hoare_triple (P) (c ()) Q \<Longrightarrow>  
  hoare_triple (\<lambda>_. P s) (bindCont (setState s) c) Q"
  apply (clarsimp simp:  hoare_triple_def   Sup_le_iff run_setState_distrib)
  apply (safe)
   apply (rule order_trans)
    apply (rule seq_mono)
     apply (rule run_setState_le)
    apply (assumption)
   apply (rule hoare_chain')
   apply (blast)
 apply (rule order_trans)
    apply (rule seq_mono)
     apply (rule run_setState_le)
   apply (assumption)
  by (simp add: assert_bot)
  

lemma fail_wp[wp]: "hoare_triple  \<bottom> (bindCont fail c) Q" 
  using run_fail_assert_valid by force

lemma assert_wp[wp]: 
  "hoare_triple ( P) (c ()) Q \<Longrightarrow>
   hoare_triple ( (\<lambda>x. (C x \<longrightarrow> P x) \<and> C x))  (do {x <- (assertion C); c x}) Q"
  apply (clarsimp split: if_splits)
  apply (clarsimp simp: assertion_def)
 
  apply (rule hoare_weaken_pre)
   apply (wp)
  apply (safe)
  apply (clarsimp)
  done



lemma "hoare_triple ( (maps_to a x \<and>* maps_to b y \<and>* maps_to c z)) (set_max a b c) ( (maps_to a x \<and>* maps_to b y \<and>* maps_to c (max x y)))"
  apply (clarsimp simp: set_max_def)
  apply (rule hoare_weaken_pre)
   apply (wp)
  apply (safe)
  apply (sep_cancel)+
  apply (clarsimp split: if_splits)
  apply (safe)
   apply (sep_cancel)+
   apply (clarsimp simp: max_def)
   apply (sep_cancel)+
  apply (clarsimp simp: max_def)
  done


lemma add_wp[wp]: "hoare_triple (P (n + m)) (c (n + m)) Q \<Longrightarrow>
  hoare_triple (\<lambda>s. n \<le> n + m \<and> (n \<le> n + m \<longrightarrow> P (n + m) s)) 
(do {x <- (n .+ m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp:  word_unsigned_add_def )
   apply (simp only: Let_unfold)
   apply (wp, clarsimp simp: bindCont_return')
  done


lemma add_wp_slot[wp]: "hoare_triple (P ((n :: Slot) + m)) (c (n + m)) Q \<Longrightarrow>
  hoare_triple (\<lambda>s. n \<le> n + m \<and> (n \<le> n + m \<longrightarrow> P (n + m) s)) 
(do {x <- (n .+ m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp: slot_unsigned_add_def word_unsigned_add_def)
   apply (simp only: Let_unfold)
   apply (wp, clarsimp simp: bindCont_return' plus_Slot_def)
    apply assumption
   apply wp
  apply (clarsimp simp: plus_Slot_def)
  apply safe
  apply (fastforce simp: less_eq_Slot_def)
  done

lemma mod_wp[wp]: "hoare_triple (P (n mod m)) (c (n mod m)) Q \<Longrightarrow>
  hoare_triple (\<lambda>s. m \<noteq> 0 \<and> (m \<noteq> 0 \<longrightarrow> P (n mod m) s))
(do {x <- (n .% m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold word_unsigned_mod_def)
   apply wp
  apply fastforce
  done

lemma div_wp[wp]: "hoare_triple (P (n div m)) (c (n div m)) Q \<Longrightarrow>
  hoare_triple (\<lambda>s. m \<noteq> 0 \<and> (m \<noteq> 0 \<longrightarrow> P ( n div m) s)) 
(do {x <- (word_unsigned_div n m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold word_unsigned_div_def, wp)
   apply (clarsimp simp: bindCont_return')
  done

lemma vector_index_wp[wp]: "hoare_triple (P (vector_inner v ! unat i)) (c (vector_inner v ! unat i)) Q \<Longrightarrow>
  hoare_triple (\<lambda>s. unat i < length (vector_inner v) \<and> length (vector_inner v) < 2^64 \<and>
    (unat i < length (vector_inner v) \<and> length (vector_inner v) < 2^64 \<longrightarrow> P (vector_inner v ! unat i) s))
(do { x <- vector_index v i; c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold vector_index_def)
   apply wp
    apply (clarsimp simp: bindCont_return')
    apply assumption
   apply wp
  apply safe
  apply (case_tac v)
  by (fastforce simp: vector_inner_def intro!: unat_ucast_less_no_overflow)

end

context hoare_logic begin
(*



term list_update


definition list_update_opt ::
  "'e list \<Rightarrow> u64 \<Rightarrow> 'e \<Rightarrow> 'e list option"
  where
  "list_update_opt xs i x \<equiv> do {
    if u64_to_nat i < length (list_inner xs) then
      Some (List (List.list_update (list_inner xs) (u64_to_nat i) x))
    else
      None
  }"


definition "validator n = Lens ((\<lambda>xs. list_index xs n) \<circ>\<^sub>m validators_f)
                               (\<lambda>a b. let (new_list :: Validator List option) = do {x <- b;  xs <- (validators_f a); list_update_opt xs n x}
                                in a\<lparr>validators_f := new_list\<rparr> )"
lemma lift_option_wp[wp]: 
  "(\<And>x. f = Some x \<Longrightarrow> hoare_triple ( P x) (c x) Q) \<Longrightarrow>
    hoare_triple (\<lambda>s. (f \<noteq> None \<longrightarrow> P (the f) s) \<and> f \<noteq> None) (do {x <- lift_option f ; c x}) Q"
  apply (clarsimp simp: lift_option_def)
  apply (safe)
  apply (rule hoare_weaken_pre)
    apply (wp)
  apply (clarsimp)
  apply (clarsimp simp: bindCont_return')
  done
*)
lemma fold_increasing_when: "finite S \<Longrightarrow> (\<And>x y. f y x \<ge> x) \<Longrightarrow> comp_fun_commute_on (insert x S) f \<Longrightarrow> Finite_Set.fold f (\<bottom> :: 'e :: {order_bot}) (S) \<le> Finite_Set.fold f \<bottom> (insert x S)"
  apply (case_tac "x \<in> S"; clarsimp?)
  apply (simp add: insert_absorb)
  apply (subst comp_fun_commute_on.fold_rec) back
      defer
      apply (rule order_refl)
     apply (clarsimp)
    apply (blast)
   apply (clarsimp)
  apply (assumption)
  done

lemma fold_increasing_when': "finite S \<Longrightarrow> (\<And>x y. f y x \<ge> x) \<Longrightarrow> comp_fun_commute_on (S) f \<Longrightarrow> Finite_Set.fold f (a :: 'e :: {order}) (S - {x}) \<le> Finite_Set.fold f a (S)"
  apply (case_tac "x \<in> S"; clarsimp?)
  apply (subst comp_fun_commute_on.fold_rec) back
      apply (assumption)
     apply clarsimp
  apply clarsimp
   apply (blast)
  apply (blast)
  done

lemma append_sorted_list_of_setD: "finite xs  \<Longrightarrow> a # x = sorted_list_of_set xs \<Longrightarrow>sorted_list_of_set (xs - {a}) = x "
  apply (case_tac "xs = {}"; clarsimp?)
  apply (induct xs rule: finite.induct; clarsimp)
  by (metis finite.insertI insert_not_empty list.inject 
            sorted_list_of_set.sorted_key_list_of_set_insert_remove sorted_list_of_set_nonempty)

lemma inj_image_sub: "inj f \<Longrightarrow> f ` (xs - {a}) = f ` xs - {f a}" 
  apply (safe; clarsimp)
   apply (simp add: injD)
  by blast

lemma commutative_insort_foldr: "comp_fun_commute_on (list.set (a#xs)) f \<Longrightarrow> foldr f (insort a xs) z = f a (foldr f xs z)"
  apply (induct xs; clarsimp)
  apply (drule meta_mp)
  apply (metis comp_fun_commute_on_def insert_iff)
  apply (clarsimp)
  by (simp add: comp_fun_commute_on.fun_left_comm)


lemma uadd_welldf: "u64_to_nat (a :: 64 word) + u64_to_nat b < 2^64 \<Longrightarrow> word_unsigned_add a  b = return (a + b)"
  apply (clarsimp simp: word_unsigned_add_def Let_unfold)
  apply (erule notE)
  by (unat_arith, clarsimp)

lemma foldr_is_fold: "finite S \<Longrightarrow> comp_fun_commute_on S f \<Longrightarrow> xs = sorted_list_of_set S \<Longrightarrow> 
  foldr f ( xs) z =  Finite_Set.fold f z S"
  apply (clarsimp)
  apply (thin_tac "xs = sorted_list_of_set S")
  apply (induct S rule:finite.induct; clarsimp)
  apply (case_tac "a \<in> A"; clarsimp?)
   apply (simp add: insert_absorb sorted_list_of_set.fold_insort_key.remove)
  apply (drule meta_mp)
   apply (simp add: comp_fun_commute_on_def)
  apply (subst comp_fun_commute_on.fold_rec[rotated], rule order_refl, clarsimp, blast, assumption)
  apply (clarsimp)
  by (subst commutative_insort_foldr, clarsimp, clarsimp)



lemma u64_add_is_commutative: " comp_fun_commute_on xs (\<lambda>x acc. bindCont acc (word_unsigned_add x))"
  apply (clarsimp simp: comp_fun_commute_on_def, rule ext, clarsimp)
  apply (rule ext, clarsimp simp: bindCont_def)
  apply (rule_tac f=xa in arg_cong)
  apply (rule ext, clarsimp simp: word_unsigned_add_def Let_unfold return_def fail_def, safe)
      apply (smt (verit, ccfv_SIG) add.left_commute le_no_overflow return_def)
  using olen_add_eqv word_plus_mono_right2 apply blast
  using olen_add_eqv word_random apply blast
   apply (metis add.left_commute le_no_overflow)
  by (simp add: add.left_commute le_no_overflow)

lemma [simp]:"comp_fun_commute_on (S :: nat set) (+)"
  by (clarsimp simp: comp_fun_commute_on_def, rule ext, clarsimp)

(*
lemma "mono f \<Longrightarrow> map f (insort a xs) = insort (f a) (map f xs)" 
  apply (induct xs; clarsimp)
  apply (safe)
  using monoD apply blast
  using monoD apply blast
   apply (simp add: monoD order_antisym)
*)

lemma idk: "finite S \<Longrightarrow> xs = sorted_list_of_set S \<Longrightarrow> mono f \<Longrightarrow> inj f \<Longrightarrow>
  map f xs = sorted_list_of_set (f ` S)"
  apply (induct S  arbitrary: xs rule: finite.inducts, clarsimp)
  apply (clarsimp)
  apply (case_tac "a \<in> A"; clarsimp?)
   apply (metis finite_imageI image_eqI sorted_list_of_set.fold_insort_key.remove)
  apply (simp add: map_insort_sorted)
  by (simp add: inj_image_mem_iff)

lemma foldr_safe_add_is_add: "(foldr (\<lambda>x acc. bindCont acc ((.+) x)) x (return (0 :: 64 word))) \<noteq> fail \<Longrightarrow> 
       return (foldr ((+) \<circ> unat) x (0 :: nat)) = 
       (do {x <- (foldr (\<lambda>x acc. bindCont acc ((.+) x)) x (return (0 :: 64 word))); return (unat x)})"
  apply (induct x  ; clarsimp)
   apply (simp add: bindCont_return')
  apply (clarsimp simp: bindCont_return' bindCont_return word_unsigned_add_def)
  apply (rule ext, clarsimp simp: return_def)
  apply (clarsimp simp: bind_eq_Some_conv)
  by (smt (verit, ccfv_SIG) bind_eq_Some_conv check_bin_op_def 
     check_bin_op_then_def option.distinct(1) option.inject u64_add_def u64_to_nat.simps)

lemma safe_sum_boundedI: "finite xs \<Longrightarrow> (\<And>x. Finite_Set.fold (+) 0 (unat ` xs) < 2 ^ 64) \<Longrightarrow> (\<exists>y. safe_sum xs = return y)"
  sorry
  apply (clarsimp simp: safe_sum_def)
  apply (induct \<open>sorted_list_of_set xs\<close> arbitrary: xs)
   apply (clarsimp)
   apply (rule_tac x=0 in exI)
  apply (clarsimp simp: foldrM_def)
  apply (clarsimp)
  apply (atomize)
  apply (clarsimp)
  apply (erule_tac x="xs - {a}" in allE)
  apply (drule mp, clarsimp?)
   apply (rule sym)
  thm append_sorted_list_of_setD
   apply (erule  append_sorted_list_of_setD[rotated])
  using finite_code apply blast
  apply (drule mp, clarsimp)
  apply (drule mp)
   apply (erule le_less_trans[rotated])
   apply (subst inj_image_sub)
  apply simp
    apply (meson injI u64_to_nat_bij)
   apply (rule fold_increasing_when')
     apply (clarsimp)
    apply (linarith)
   apply (simp add: comp_fun_commute_on_def)
   apply (clarsimp)
   apply (rule ext, clarsimp)
  apply (clarsimp)
  apply (subgoal_tac "a \<in> xs")
  apply (clarsimp simp: append_sorted_list_of_setD)
   apply (rule subst, assumption)
  apply (subst foldrM_def)
  apply (subst foldr_Cons)
   apply (clarsimp)
   apply (subst (asm) foldr_is_fold[symmetric], clarsimp, clarsimp)
    apply (rule idk, assumption, assumption)
  using less_eq_u64_def monoI apply blast
    apply (simp add: inj_def u64_to_nat_bij)
   apply (subst (asm) list.map(2), simp)

   apply (rule uadd_welldf)
   apply (clarsimp simp: foldr_map)
  thm arg_cong
   apply (frule arg_cong[where f="u64_to_nat o the"], clarsimp)
  apply (subgoal_tac "foldr ((+) \<circ> u64_to_nat) x 0 = u64_to_nat (the (foldr (\<lambda>x acc. acc \<bind> (.+) x) x (Some (u64.u64 0))))")
  
    apply (clarsimp)
   apply (rule foldr_safe_add_is_add, assumption)
  by (metis insertCI list.simps(15) sorted_list_of_set.set_sorted_key_list_of_set)
end
end

definition get_current_epoch :: "(Epoch, 'a) cont" where
  "get_current_epoch \<equiv> do {
     s <- read beacon_slots;
     current_epoch <- lift_option ( (slot_to_u64 s) \\ SLOTS_PER_EPOCH config);
     return (Epoch current_epoch)}"

lemma get_total_active_balance_wp[wp]: 
 "(\<And>x. \<lblot>P x\<rblot> (c x) \<lblot>Q\<rblot>) \<Longrightarrow> (slot_to_u64 slots \\ SLOTS_PER_EPOCH config) = Some current_epoch \<Longrightarrow>
  active_validators = [i. (i, v) \<leftarrow> enumerate (list_inner vs), is_active_validator v (Epoch current_epoch)] \<Longrightarrow>
  s_balances = undefined \<Longrightarrow>
  max (EFFECTIVE_BALANCE_INCREMENT config) s_balances = y \<Longrightarrow>   
   \<lblot> (maps_to (validators) vs \<and>* maps_to beacon_slots slots \<and>* 
     ((maps_to validators vs \<and>* maps_to beacon_slots slots)\<longrightarrow>* P y)) \<rblot>
   do {x <- get_total_active_balance ; c x}
   \<lblot>Q\<rblot>"
 apply (clarsimp simp: get_total_active_balance_def get_current_epoch_def)
  apply (rule hoare_weaken_pre)
   apply (wp)

   apply (clarsimp simp: get_active_validator_indices_def, wp)
   apply (clarsimp simp: get_total_balance_def, wp)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (safe, sep_cancel+)
   apply (clarsimp)
  apply (safe; clarsimp?)
   apply (rule safe_sum_boundedI, rule finite_imageI)

lemma get_total_active_balance_wp[wp]: 
 "\<lblot> (maps_to (validators) vs \<and>* maps_to beacon_slots slots \<and>* R) \<rblot>
   get_total_active_balance \<lblot>(maps_to validators vs \<and>* maps_to beacon_slots slots \<and>* R)\<rblot>"
  apply (clarsimp simp: get_total_active_balance_def get_current_epoch_def)
  apply (rule hoare_weaken_pre)
   apply (wp)
   apply (clarsimp simp: get_active_validator_indices_def)
   apply (clarsimp simp: get_total_balance_def, wp)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (safe, sep_cancel+)
   apply (clarsimp)
   apply (rule safe_sum_boundedI, rule finite_imageI)
  apply (clarsimp)
   apply (clarsimp)
  sorry

lemma  get_base_reward_per_increment_wp: 
 "\<lblot> (maps_to (validator index) v \<and>* R) \<rblot>
                 (get_base_reward_per_increment )  \<lblot>(maps_to (validator index) v \<and>* R)\<rblot>"
  apply (clarsimp simp: get_base_reward_per_increment_def)
  apply (rule hoare_weaken_pre)

  apply (wp)

lemma get_base_reward_wp: 
  "\<lblot> (maps_to (validator index) v \<and>* R) \<rblot>
                 (get_base_reward index)  \<lblot>(maps_to (validator index) v \<and>* R)\<rblot>"
  apply (clarsimp simp: get_base_reward_def)
  apply (rule hoare_weaken_pre)

   apply (wp)
   apply (clarsimp simp: get_base_reward_per_increment_def get_total_active_balance_def get_current_epoch_def)
  apply (wp)




end


end
*)