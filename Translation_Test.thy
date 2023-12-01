theory Translation_Test
  imports "algebra/Traces" ProcessEpoch "Word_Lib.Word_64" "Word_Lib.More_Arithmetic"
begin

locale verified_con = constrained_atomic +
  constrains pgm  :: "BeaconState rel \<Rightarrow> 'a"
  constrains env  :: "BeaconState rel \<Rightarrow> 'a"
  constrains test :: "BeaconState set \<Rightarrow> 'a"
  fixes config :: "Config"

begin

lemma nil_not_top[simp]: "(nil = \<top>) = False"
  by (metis (full_types) UNIV_I abstract_hom_commands.hom_iso_eq empty_iff seq_abort seq_nil_left
      test.abstract_hom_commands_axioms)

definition pick_state :: "(BeaconState \<Rightarrow> 'b) \<Rightarrow> ('b, 'a) cont" where
  "pick_state f \<equiv> do { state \<leftarrow> getState; return (f state) }"

(* word-based arithmetic *)
definition add :: "64 word \<Rightarrow> 64 word \<Rightarrow> (64 word, 'a) cont" where
  "add x y \<equiv> do {
     let result = x + y;
     if x < result then return result else fail
   }"

lemma add_sanity: "x < 2^64 - 2 \<Longrightarrow> run (add x 1) \<noteq> \<top>"
  by (clarsimp simp: add_def run_def Let_unfold return_def plus_1_less fail_def)

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
  where "set_justified_checkpoint n \<equiv> modifyState (\<lambda>state. state \<lparr> current_justified_checkpoint_f := n \<rparr>)"

end