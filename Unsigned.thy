theory Unsigned
  imports Main HOL.Nat Cont_Monad_Algebra VerifiedConsensus
begin

abbreviation nat_to_u64 :: "nat \<Rightarrow> u64" where
  "nat_to_u64 \<equiv> Word.of_nat"

abbreviation u64_to_nat :: "u64 \<Rightarrow> nat" where
  "u64_to_nat \<equiv> Word.the_nat"

primrec slot_to_u64 :: "Slot \<Rightarrow> u64" where
  "slot_to_u64 (Slot n) = n"

primrec epoch_to_u64 :: "Epoch \<Rightarrow> u64" where
  "epoch_to_u64 (Epoch n) = n"

lemma u64_upper_bound: "u64_to_nat x < 2 ^ 64"
  apply (rule Orderings.xtrans(1)[where b="2 ^ LENGTH(64)"])
   apply force
  by (metis nat_less_numeral_power_cancel_iff take_bit_int_less_exp the_nat.rep_eq)

lemma u64_to_nat_bij: "(u64_to_nat x = u64_to_nat y) = (x = y)"
  by auto

lemma slot_to_u64_bij: "(slot_to_u64 x = slot_to_u64 y) = (x = y)"
  by (case_tac x; case_tac y; auto)

lemma epoch_to_u64_bij: "(epoch_to_u64 x = epoch_to_u64 y) = (x = y)"
  by (case_tac x; case_tac y; auto)

(* Linear order instance for Slot *)
instantiation Slot :: linorder
begin

definition less_eq_Slot :: "Slot \<Rightarrow> Slot \<Rightarrow> bool" where
  "less_eq_Slot x y \<equiv> slot_to_u64 x \<le> slot_to_u64 y"

definition less_Slot :: "Slot \<Rightarrow> Slot \<Rightarrow> bool" where
  "less_Slot x y \<equiv> slot_to_u64 x < slot_to_u64 y"

instance
  by (intro_classes;
      auto intro: order_neq_le_trans simp: less_eq_Slot_def less_Slot_def slot_to_u64_bij)
end

(* Linear order instance for Epoch *)
instantiation Epoch :: linorder
begin

definition less_eq_Epoch :: "Epoch \<Rightarrow> Epoch \<Rightarrow> bool" where
  "less_eq_Epoch x y \<equiv> epoch_to_u64 x \<le> epoch_to_u64 y"

definition less_Epoch :: "Epoch \<Rightarrow> Epoch \<Rightarrow> bool" where
  "less_Epoch x y \<equiv> epoch_to_u64 x < epoch_to_u64 y"

instance
  by (intro_classes;
      auto intro: order_neq_le_trans simp: less_eq_Epoch_def less_Epoch_def epoch_to_u64_bij)
end

consts
  unsigned_add :: "'w \<Rightarrow> 'w \<Rightarrow> ('w, 'a) cont"
  unsigned_sub :: "'w \<Rightarrow> 'w \<Rightarrow> ('w, 'a) cont"
  unsigned_mul :: "'w \<Rightarrow> 'w \<Rightarrow> ('w, 'a) cont"
  unsigned_div :: "'w \<Rightarrow> 'w \<Rightarrow> ('w, 'a) cont"
  unsigned_mod :: "'w \<Rightarrow> 'w \<Rightarrow> ('w, 'a) cont"

(* word-based arithmetic with overflow checks *)
context verified_con
begin

definition word_unsigned_add :: "('w :: len) word \<Rightarrow> 'w word \<Rightarrow> ('w word, 'a) cont" where
  "word_unsigned_add x y \<equiv> do {
     let result = x + y;
     if x \<le> result then return result else fail
   }"

definition slot_unsigned_add :: "Slot \<Rightarrow> Slot \<Rightarrow> (Slot, 'a) cont" where
  "slot_unsigned_add x y \<equiv> do {
    result \<leftarrow> word_unsigned_add (slot_to_u64 x) (slot_to_u64 y);
    return (Slot result)
  }"

definition epoch_unsigned_add :: "Epoch \<Rightarrow> Epoch \<Rightarrow> (Epoch, 'a) cont" where
  "epoch_unsigned_add x y \<equiv> do {
    result \<leftarrow> word_unsigned_add (epoch_to_u64 x) (epoch_to_u64 y);
    return (Epoch result)
  }"

adhoc_overloading
  unsigned_add word_unsigned_add slot_unsigned_add epoch_unsigned_add

notation
  unsigned_add (infixl ".+" 65) and
  unsigned_sub (infixl ".-" 65) and
  unsigned_mul (infixl ".*" 70) and
  unsigned_div (infixl "\\" 70) and
  unsigned_mod (infixl ".%" 75)

lemma add_sanity: "x < 2^64 - 2 \<Longrightarrow> run (x .+ 1) \<noteq> \<top>"
  apply (clarsimp simp: word_unsigned_add_def run_def Let_unfold return_def plus_1_less fail_def)
  by (metis inc_i less_x_plus_1 olen_add_eqv order_less_imp_le word_order.extremum)

definition word_unsigned_mul :: "('w :: len) word \<Rightarrow> 'w word \<Rightarrow> ('w word, 'a) cont" where
  "word_unsigned_mul x y \<equiv>
     let result = x * y in
     if result div x = y then return result else fail"

definition slot_unsigned_mul :: "Slot \<Rightarrow> Slot \<Rightarrow> (Slot, 'a) cont" where
  "slot_unsigned_mul x y \<equiv> do {
    result \<leftarrow> word_unsigned_mul (slot_to_u64 x) (slot_to_u64 y);
    return (Slot result)
  }"

adhoc_overloading
  unsigned_mul word_unsigned_mul slot_unsigned_mul

lemma mul_sanity: "(x :: u64) = 2 ^ 63 - 1 \<Longrightarrow> y = 2 \<Longrightarrow> run (x .* y) \<noteq> \<top>"
  by (clarsimp simp: word_unsigned_mul_def run_def Let_unfold return_def)

lemma mul_sanity_overflow: "(x :: u64) = 2 ^ 63 \<Longrightarrow> y = 2 \<Longrightarrow> run (x .* y) = \<top>"
  by (clarsimp simp: word_unsigned_mul_def run_def Let_unfold return_def fail_def)

definition word_unsigned_div :: "('w :: len) word \<Rightarrow> 'w word \<Rightarrow> ('w word, 'a) cont" where
  "word_unsigned_div x y \<equiv>
     if y \<noteq> 0 then return (x div y) else fail"

definition slot_unsigned_div :: "Slot \<Rightarrow> Slot \<Rightarrow> (Slot, 'a) cont" where
  "slot_unsigned_div x y \<equiv> do {
    result \<leftarrow> word_unsigned_div (slot_to_u64 x) (slot_to_u64 y);
    return (Slot result)
  }"

adhoc_overloading
  unsigned_div word_unsigned_div slot_unsigned_div


definition word_unsigned_mod :: "('w :: len) word \<Rightarrow> 'w word \<Rightarrow> ('w word, 'a) cont" where
  "word_unsigned_mod x y \<equiv>
     if y \<noteq> 0 then return (x mod y) else fail"


adhoc_overloading
  unsigned_mod word_unsigned_mod

lemma udiv_sanity: "run ((x :: u64) \\ 2) \<noteq> \<top>"
  by (clarsimp simp: word_unsigned_div_def run_def Let_unfold return_def)

lemma udiv_sanity_overflow: "run (x \\ 0) = \<top>"
  by (clarsimp simp: word_unsigned_div_def run_def Let_unfold fail_def)

definition word_unsigned_sub :: "('w :: len) word \<Rightarrow> 'w word \<Rightarrow> ('w word, 'a) cont" where
  "word_unsigned_sub x y \<equiv>
     let result = x - y in
     if result \<le> x then return result else fail"

definition slot_unsigned_sub :: "Slot \<Rightarrow> Slot \<Rightarrow> (Slot, 'a) cont" where
  "slot_unsigned_sub x y \<equiv> do {
    result \<leftarrow> word_unsigned_sub (slot_to_u64 x) (slot_to_u64 y);
    return (Slot result)
  }"

definition epoch_unsigned_sub :: "Epoch \<Rightarrow> Epoch \<Rightarrow> (Epoch, 'a) cont" where
  "epoch_unsigned_sub x y \<equiv> do {
    result \<leftarrow> word_unsigned_sub (epoch_to_u64 x) (epoch_to_u64 y);
    return (Epoch result)
  }"

(* TODO(michael) : more epoch ops *)
adhoc_overloading
  unsigned_sub word_unsigned_sub slot_unsigned_sub epoch_unsigned_sub

lemma sub_sanity: "(x :: u64) > 1 \<Longrightarrow> run (x .- 1) \<noteq> \<top>"
  apply (clarsimp simp: word_unsigned_sub_def run_def Let_unfold return_def fail_def)
  by (metis word_not_simps(1) word_sub_1_le)

lemma u64_max: "2^64 - 1 = (-1 :: 64 word)"
  by (metis eq_2_64_0 minus_one_word word_exp_length_eq_0)

lemma sub_sanity_max: "run ((2^64 - 1) .- (x :: u64)) \<noteq> \<top>"
  apply (subst u64_max)
  by (fastforce simp: word_unsigned_sub_def run_def Let_unfold return_def fail_def)

lemma sub_sanity_overflow: "y \<noteq> 0 \<Longrightarrow> run (0 .- y) = \<top>"
  by (fastforce simp: word_unsigned_sub_def run_def Let_unfold return_def fail_def)

end

end