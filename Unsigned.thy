theory Unsigned
  imports Main HOL.Nat "Word_Lib.Word_64" "Word_Lib.Word_8" Cont_Monad_Algebra
begin

type_synonym u8 = "8 word"
type_synonym u64 = "64 word"
datatype Slot = Slot u64
datatype Epoch = Epoch u64

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

end